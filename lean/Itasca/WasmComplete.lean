import Itasca.BodyProgramComplete
import Itasca.CompletenessStep

open Aeneas Aeneas.Std

namespace Itasca.Completeness

/-- All instruction trees in the binary Wasm 1.0 profile execute successfully
when their generated typing derivation and version-specific restrictions hold. -/
theorem programs (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (henv : Wasm1.Environment env) (tokens : List Wasm.Token) (ops : List instr)
    (he : Wasm.Emits tokens ops) : Program data env ctx tokens ops := by
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

end Itasca.Completeness

namespace Itasca

/-- Completeness of the actual extracted public body validator. The premises
are independent binary provenance, generated SpecTec declarative typing,
Wasm 1.0 branch-table semantics and signatures, and existing API limits.
There is no executable checker, handler-success, or step-contract premise. -/
theorem code.validate_body.wasm_complete (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType)
    (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm1.Body data env ctx bt) :
    code.validate_body data env ctx = .ok (.Ok ()) :=
  Completeness.body_of_programs data env ctx bt hresults hsize
    (Completeness.programs data env ctx henv) hbody

/-- An explicit instruction-tree form of the public completeness theorem. -/
theorem code.validate_body.wasm_complete_of_typing (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) (ops : List instr)
    (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbytes : Wasm.BodyEncoding data ops) (htyped : Wasm.FunctionTyped env ctx bt ops)
    (hprofile : Wasm1.Instructions
      (WasmFrames.enter (EnvTranslation.context env ctx) .body bt) ops) :
    code.validate_body data env ctx = .ok (.Ok ()) :=
  code.validate_body.wasm_complete data env ctx bt henv hresults hsize
    ⟨ops, hbytes, htyped, hprofile⟩

end Itasca
