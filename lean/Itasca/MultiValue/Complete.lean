import Itasca.MultiValue.BodyComplete
import Itasca.MultiValue.CompletenessStep
import Itasca.MultiValue.Soundness

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Completeness

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

end Itasca.MultiValue.Completeness

namespace Itasca

/-- Completeness of the extracted public multi-value body validator from
independent binary encoding, generated Wasm 2.0 typing, and the independent
function-reference declaration condition. Implementation bounds constrain body
bytes and signature sizes. -/
theorem code.validate_multi_value_body.wasm_complete (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32)
    (henv : MultiValue.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : MultiValue.Validated data env locals index) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) := by
  obtain ⟨ft, ops, hi, hbytes, htyped, hdecl⟩ := hbody
  have hmem : ft ∈ env.types.val := List.mem_of_getElem? hi
  obtain ⟨hparams, hresults⟩ := henv.types ft hmem
  exact MultiValue.Completeness.body_of_programs data env locals index ft hi hparams hresults hsize
    (MultiValue.Completeness.programs data env ⟨locals, ft.results⟩ index henv
      (by simp [MultiValue.resolve, hi])) ops hbytes htyped hdecl

theorem code.validate_multi_value_body.wasm_complete_of_typing (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType) (ops : List instr)
    (henv : MultiValue.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hi : env.types.val[index.val]? = some ft)
    (hbytes : MultiValue.BodyEncoding data ops) (htyped : MultiValue.FunctionTyped env locals ft ops)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) :=
  code.validate_multi_value_body.wasm_complete data env locals index henv hsize ⟨ft, ops, hi, hbytes, htyped, hdecl⟩

theorem code.validate_multi_value_body.wasm_accepts_iff (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32)
    (henv : MultiValue.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) ↔
      MultiValue.Validated data env locals index :=
  ⟨code.validate_multi_value_body.wasm_sound data env locals index,
    code.validate_multi_value_body.wasm_complete data env locals index henv hsize⟩

end Itasca
