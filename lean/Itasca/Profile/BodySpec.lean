import Itasca.Profile.Types
import Itasca.Profile.Instructions
import Itasca.Wasm2.BodySpec

/-!
# Profile function-body specification

`Profile.Body` is the profile-parametric statement that a function body is valid: exact body bytes
(`BodyEncoding`), declarative typing under `functionContext`, the profile restrictions, and
declared references, for the signature the environment gives the function.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The profile's grammar relates the exact body bytes, including the final `end`, to the
instruction tree `ops`. It does not execute the validator or impose implementation limits. -/
def BodyEncoding (profile : ValidationProfile) (data : Slice U8) (ops : List instr) : Prop :=
  match profile with
  | .Wasm1 => Wasm1.BodyEncoding data ops
  | .Wasm2 => Wasm2.BodyEncoding data ops

/-- The context for a function body: the result label followed by the Wasm 2.0 body context. -/
def functionContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context :=
  Control.labelContext (ft.results.val.map Translate.valueType) ++
    Wasm2.bodyContext env locals ft

/-- The semantic specification of a valid function body, shared by both profiles. The signature
comes from the environment's type `index`, and the bytes, typing and profile restrictions all
describe the same instruction tree. Resource bounds are separate. -/
def Body (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ FuncType profile ft ∧
    BodyEncoding profile data ops ∧ Wasm2.FunctionTyped env locals ft ops ∧
    Instructions profile (functionContext env locals ft) ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) ops

end Itasca.Profile
