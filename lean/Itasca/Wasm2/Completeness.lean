import Itasca.Wasm2.Complete.Control
import Itasca.Wasm2.Execution
import Itasca.Wasm2.Complete.LeafContracts
import Itasca.Wasm2.Soundness

/-!
# Wasm 2.0 body completeness

Completeness of the extracted body validator from independent premises. `code.bodyCore.complete`
accepts every `Wasm2.Validated` body of a profile within the implementation limits. The
per-opcode contracts it builds on are in `Wasm2/Complete/`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- A body with independent encoding, typing and declared references is accepted, given a
`Program` contract for every token sequence. Typing starts the body with no operands, even when
its type has parameters, and the final `end` closes the selected result signature. -/
theorem body_of_programs (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Emits tokens ops →
      Program data env profile ⟨locals, ft.results⟩ index tokens ops)
    (ops : List instr)
    (hencoding : ∃ tokens next, ProfileConsumed profile data 0#usize tokens next ∧
      next.val = data.length ∧ BodyTokens tokens ops)
    (htyped : FunctionTyped env locals ft ops)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops)
    (hprofile : profile = .Wasm1 → Wasm1.Instructions (functionContext env locals ft) ops) :
    code.bodyCore data env locals results index profile = .ok (.Ok ()) := by
  obtain ⟨tokens, next, hbytes, hfinish, inner, heq, hemits⟩ := hencoding
  subst tokens
  obtain ⟨middle, hinner, hend⟩ := hbytes.split
  let st := initial index
  let f : Frame st :=
    ⟨⟨[], ⟨.Body, .TypeIndex index, 0#usize, false⟩, [], [], rfl, rfl, rfl⟩,
      [], .TypeIndex index, rfl, rfl⟩
  let C := Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft
  have hmatch : EnvTranslation.Matches env ⟨locals, ft.results⟩ C :=
    (EnvTranslation.Matches.root env ⟨locals, ft.results⟩).enter _
  have hlabels : Labels env st C := by
    intro depth
    cases depth with
    | zero => simp [C, st, initial, Control.labelContext_labels, labelTypes, labelAt, target, outputs, resolve, hi]
    | succ depth => simp [C, st, initial, Control.labelContext_labels, bodyContext,
        EnvTranslation.context, labelTypes, labelAt]
  have hbounds : Bounds data st := by
    constructor <;> simp [st, initial, hsize]
  obtain ⟨s, hrun, hp, hout, _⟩ := hprograms inner ops hemits C st f middle []
    (ft.results.val.map Translate.valueType) hmatch hlabels hbounds hinner
      (Sequence.realizes_default false []) htyped hdecl hprofile
  obtain ⟨g, hgp, hgc, hcp, hco, hck, hcbase, hreal⟩ := hout.next
  obtain ⟨last, hclose, hp', hc', hb', _⟩ := execute_end g data env profile ⟨locals, ft.results⟩
    index next ft.params.val ft.results.val (by simpa [hp] using hend.single.1)
    (by simp [hgc, f, inputs, resolve, hi]) (by simp [hgc, f, outputs, resolve, hi])
    (by simp [hck, f]) hreal (by simp [hco, f])
  apply ((hrun.append hclose).change_context ⟨locals, results⟩ rfl).public
    hi hparams hresults hsize
  · simpa [hgp, f] using hb'
  · simpa [hp'] using hfinish

end Itasca.Wasm2.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- Every token sequence emitted by a syntax tree has a `Program` contract for arbitrary
environments within limits. -/
theorem programs (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (henv : Profile.EnvironmentWithinLimits env)
    (hret : resolve env (.Type index .Results) = some ctx.results.val)
    (tokens : List Token) (ops : List instr) (he : Emits tokens ops) :
    Program data env profile ctx index tokens ops := by
  apply program_of_atoms data env profile ctx index ?_ tokens ops he
  intro tokens op ha smaller
  cases ha with
  | simple hs =>
    cases hs with
    | plain op _ =>
      exact atom_of_leaf data env profile ctx index
        (leaf_contract data env profile ctx index henv hret) op
  | block bt hb => exact atom_block henv bt hb smaller
  | loop bt hb => exact atom_loop henv bt hb smaller
  | ifElse bt hy hn => exact atom_ifElse henv bt hy hn smaller
  | ifEnd bt hb => exact atom_ifEnd henv bt hb smaller

end Itasca.Wasm2.Completeness

namespace Itasca

/-- Completeness of `code.bodyCore` for either profile from independent binary encoding,
generated Wasm 2.0 typing, the independent function-reference declaration condition, and for
Wasm 1.0 the Wasm 1.0 grammar and restrictions. Implementation bounds constrain body bytes and
signature sizes. -/
theorem code.bodyCore.complete (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (profile : ValidationProfile)
    (henv : Profile.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated profile data env locals index) :
    code.bodyCore data env locals results index profile = .ok (.Ok ()) := by
  obtain ⟨ft, ops, hi, hbytes, htyped, hdecl, hwasm1⟩ := hbody
  have hmem : ft ∈ env.types.val := List.mem_of_getElem? hi
  obtain ⟨hparams, hresults⟩ := (henv.types ft hmem).bounds
  have hencoding : ∃ tokens next, ProfileConsumed profile data 0#usize tokens next ∧
      next.val = data.length ∧ Wasm2.BodyTokens tokens ops := by
    cases profile with
    | Wasm1 => exact (hwasm1 rfl).1
    | Wasm2 => exact hbytes
  exact Wasm2.Completeness.body_of_programs data env profile locals results index ft hi hparams
    hresults hsize
    (Wasm2.Completeness.programs data env profile ⟨locals, ft.results⟩ index henv
      (by simp [Wasm2.resolve, hi])) ops hencoding htyped hdecl (fun hp => (hwasm1 hp).2)

end Itasca
