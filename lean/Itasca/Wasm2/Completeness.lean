import Itasca.Wasm2.Complete.Control
import Itasca.Wasm2.Execution
import Itasca.Wasm2.Complete.LeafContracts
import Itasca.Wasm2.Soundness

/-!
# Wasm 2.0 body completeness

Completeness of the extracted `code.validate_multi_value_body` (which validates all of Wasm 2.0)
from independent premises. `code.validate_multi_value_body.wasm_complete` accepts every
`Wasm2.Validated` body within the implementation limits, and `wasm_accepts_iff` combines it with
soundness from `Wasm2/Soundness`. The per-opcode contracts it builds on are in `Wasm2/Complete/`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- A body with independent encoding, typing and declared references is accepted, given a
`Program` contract for every token sequence. Typing starts the body with no operands, even when
its type has parameters, and the final `end` closes the selected result signature. -/
theorem body_of_programs (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Emits tokens ops →
      Program data env ⟨locals, ft.results⟩ index tokens ops)
    (ops : List instr) (hencoding : BodyEncoding data ops)
    (htyped : FunctionTyped env locals ft ops)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) := by
  obtain ⟨tokens, next, hbytes, hfinish, inner, heq, hemits⟩ := hencoding
  subst tokens
  obtain ⟨middle, hinner, hend⟩ := Consumed.split hbytes
  let st := initial index
  let f : Frame st :=
    ⟨⟨[], ⟨.Body, .Empty, .TypeIndex index, 0#usize, false⟩, [], [], rfl, rfl, rfl⟩,
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
      (Sequence.realizes_default false []) htyped hdecl
  obtain ⟨g, hgp, hgc, hcp, hco, hck, hcb, hcbase, hreal⟩ := hout.next
  obtain ⟨last, hclose, hp', hc', hb', _⟩ := execute_end g data env ⟨locals, ft.results⟩
    index next ft.params.val ft.results.val (by simpa [hp] using hend.single)
    (by simp [hgc, f, inputs, resolve, hi]) (by simp [hgc, f, outputs, resolve, hi])
    (by simp [hck, f]) hreal (by simp [hco, f])
  apply ((hrun.append hclose).change_context ⟨locals, alloc.vec.Vec.new _⟩ rfl).public
    hi hparams hresults hsize
  · simpa [hgp, f] using hb'
  · simpa [hp'] using hfinish

end Itasca.Wasm2.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- Every token sequence emitted by a syntax tree has a `Program` contract for arbitrary
environments within limits. -/
theorem programs (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (henv : EnvironmentWithinLimits env)
    (hret : resolve env (.Type index .Results) = some ctx.results.val)
    (tokens : List Token) (ops : List instr) (he : Emits tokens ops) :
    Program data env ctx index tokens ops := by
  apply program_of_atoms data env ctx index ?_ tokens ops he
  intro tokens op ha smaller
  cases ha with
  | simple hs =>
    cases hs with
    | plain op _ => exact atom_of_leaf data env ctx index (leaf_contract data env ctx index henv hret) op
  | block bt hb => exact atom_block henv bt hb smaller
  | loop bt hb => exact atom_loop henv bt hb smaller
  | ifElse bt hy hn => exact atom_ifElse henv bt hy hn smaller
  | ifEnd bt hb => exact atom_ifEnd henv bt hb smaller

end Itasca.Wasm2.Completeness

namespace Itasca

/-- Completeness of the extracted public body validator from
independent binary encoding, generated Wasm 2.0 typing, and the independent
function-reference declaration condition. Implementation bounds constrain body
bytes and signature sizes. -/
theorem code.validate_multi_value_body.wasm_complete (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32)
    (henv : Wasm2.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm2.Validated data env locals index) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) := by
  obtain ⟨ft, ops, hi, hbytes, htyped, hdecl⟩ := hbody
  have hmem : ft ∈ env.types.val := List.mem_of_getElem? hi
  obtain ⟨hparams, hresults⟩ := henv.types ft hmem
  exact Wasm2.Completeness.body_of_programs data env locals index ft hi hparams hresults hsize
    (Wasm2.Completeness.programs data env ⟨locals, ft.results⟩ index henv
      (by simp [Wasm2.resolve, hi])) ops hbytes htyped hdecl

/-- `wasm_complete` with the `Wasm2.Validated` witnesses supplied as separate premises. -/
theorem code.validate_multi_value_body.wasm_complete_of_typing (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType) (ops : List instr)
    (henv : Wasm2.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hi : env.types.val[index.val]? = some ft)
    (hbytes : Wasm2.BodyEncoding data ops) (htyped : Wasm2.FunctionTyped env locals ft ops)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) :=
  code.validate_multi_value_body.wasm_complete data env locals index henv hsize ⟨ft, ops, hi, hbytes, htyped, hdecl⟩

/-- Within the implementation limits, the body validator accepts exactly the `Wasm2.Validated`
bodies. -/
theorem code.validate_multi_value_body.wasm_accepts_iff (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32)
    (henv : Wasm2.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) ↔
      Wasm2.Validated data env locals index :=
  ⟨code.validate_multi_value_body.wasm_sound data env locals index,
    code.validate_multi_value_body.wasm_complete data env locals index henv hsize⟩

end Itasca
