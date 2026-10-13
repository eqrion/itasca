import Itasca.Wasm1.Complete.Structured
import Itasca.Wasm1.Complete.LeafContracts

/-!
# Wasm 1.0 body completeness

`code.validate_body.wasm_complete` shows that `code.validate_body` accepts every body satisfying
`Wasm1.Body`, given the size cap, the result shape and `Wasm1.Environment`. The proof composes
the program executions of `Wasm1/Complete/` (`Wasm1.Completeness.programs`) and closes the body
frame in `Wasm1.Completeness.body_of_programs`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

/-- Given executions for every emitted token list, a body in `Wasm1.Body` is accepted. The proof
closes the body frame after the instruction list and discharges the size and trailing-byte
guards. -/
theorem body_of_programs (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Wasm1.Emits tokens ops → Program data env ctx tokens ops)
    (hbody : Wasm1.Body data env ctx bt) :
    code.validate_body data env ctx = .ok (.Ok ()) := by
  obtain ⟨ops, hencoding, htyped, hprofile⟩ := hbody
  obtain ⟨tokens, next, hbytes, hfinish, inner, heq, hemits⟩ := hencoding
  subst tokens
  obtain ⟨middle, hinner, hend⟩ := Wasm1.Consumed.split hbytes
  let st := Wasm1.Loop.initial bt
  let f : Frame st :=
    ⟨[], ⟨.Body, bt, Control.signature bt, 0#usize, false⟩, [], [], rfl, rfl, rfl⟩
  let C := Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt
  have hmatch : EnvTranslation.Matches env ctx C :=
    (EnvTranslation.Matches.root env ctx).enter _
  have hlabels : C.LABELS = Control.labels st.ctrls.val := by
    change [list.mk_list (Control.resultTypes bt)] =
      [list.mk_list ((Control.results bt).map Translate.valueType)]
    rfl
  have hbounds := (Wasm1.State.start data env ctx bt hsize).bounds
  obtain ⟨s, hrun, hp, hout, hb⟩ := hprograms inner ops hemits C st f middle []
    (Control.resultTypes bt) hmatch hlabels hbounds hinner
      (Sequence.realizes_default false []) htyped hprofile
  obtain ⟨g, hgp, hgo, hgk, hgb, hgsig, hgba, hgr⟩ := hout.next
  have hend' : Wasm1.At data s.pos .end_ next := by simpa [hp] using hend.single
  have hthen : g.current.kind = .Then → g.current.block_type = .Empty := by
    simp [hgk, f]
  have hreal : Sequence.Realizes g.current.polymorphic_base g.operands
      (Control.resultTypes g.current.block_type) := by simpa [hgb, f] using hgr
  obtain ⟨last, hrun', hp', hc', _, _⟩ := execute_end g data env ctx next hb hend' hthen hreal
  apply (hrun.append hrun').public hresults hsize
  · simpa [hgp, f] using hc'
  · simpa [hp'] using hfinish

end Itasca.Wasm1.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

/-- Every emitted token list for Wasm 1.0 has a successful program execution. -/
theorem programs (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (henv : Wasm1.Environment env) (tokens : List Wasm1.Token) (ops : List instr)
    (he : Wasm1.Emits tokens ops) : Program data env ctx tokens ops := by
  apply program_of_atoms data env ctx ?_ tokens ops he
  intro tokens op ha smaller
  cases ha with
  | simple hs =>
    cases hs with
    | plain op _ => exact atom_of_leaf data env ctx (leaf_contract data env ctx henv) op
  | block bt hb => exact atom_block bt hb smaller
  | loop bt hb => exact atom_loop bt hb smaller
  | ifElse bt hy hn => exact atom_ifElse bt hy hn smaller
  | ifEnd bt hb => exact atom_ifEnd bt hb smaller

end Itasca.Wasm1.Completeness

namespace Itasca

/-- Completeness of the extracted `code.validate_body`. The premises are independent binary
provenance, generated SpecTec typing, the Wasm 1.0 profile, the signature tables and the API
size cap. There is no premise about handler success or step contracts. -/
theorem code.validate_body.wasm_complete (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm1.Body data env ctx bt) :
    code.validate_body data env ctx = .ok (.Ok ()) :=
  Wasm1.Completeness.body_of_programs data env ctx bt hresults hsize
    (Wasm1.Completeness.programs data env ctx henv) hbody

/-- `code.validate_body.wasm_complete` with the instruction list given explicitly. -/
theorem code.validate_body.wasm_complete_of_typing (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) (ops : List instr)
    (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbytes : Wasm1.BodyEncoding data ops) (htyped : Wasm1.FunctionTyped env ctx bt ops)
    (hprofile : Wasm1.Instructions
      (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops) :
    code.validate_body data env ctx = .ok (.Ok ()) :=
  code.validate_body.wasm_complete data env ctx bt henv hresults hsize
    ⟨ops, hbytes, htyped, hprofile⟩

end Itasca
