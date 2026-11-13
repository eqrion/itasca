import Itasca.Profile.Types
import Itasca.Wasm2.BodySpec

/-!
# Profile function-body specification

`Profile.Body` is the profile-parametric statement that a function body is valid: exact body bytes
(`BodyEncoding`), declarative typing under `Wasm2.functionContext`, and
declared references, for the signature the environment gives the function.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- The profile's grammar relates the exact body bytes, including the final `end`, to the
instruction tree `ops`. It does not execute the validator or impose implementation limits. -/
def BodyEncoding (profile : ValidationProfile) (data : Slice U8) (ops : List instr) : Prop :=
  Wasm2.BodyEncoding data ops

/-- The semantic specification of a valid function body. The signature
comes from the environment's type `index`, and the bytes and typing
describe the same instruction tree. Resource bounds are separate. -/
def Body (profile : ValidationProfile) (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧
    BodyEncoding profile data ops ∧ Wasm2.FunctionTyped env locals ft ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) ops

end Itasca.Profile
