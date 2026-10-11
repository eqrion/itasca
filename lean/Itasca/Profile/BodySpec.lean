import Itasca.Profile.Types
import Itasca.Profile.Instructions
import Itasca.MultiValue.Body

open Aeneas Aeneas.Std

namespace Itasca.Profile

/-- Exact body bytes, including the final end. This relation does not execute
the validator and does not impose implementation limits. -/
def BodyEncoding (profile : ValidationProfile) (data : Slice U8) (ops : List instr) : Prop :=
  match profile with
  | .Wasm1 => Wasm.BodyEncoding data ops
  | .MultiValue => MultiValue.BodyEncoding data ops

def functionContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context :=
  Control.labelContext (ft.results.val.map Translate.valueType) ++
    MultiValue.bodyContext env locals ft

/-- A common semantic boundary for function validation. The selected signature
comes from the actual environment; bytes, typing, and version restrictions
refer to the same instruction tree. Resource bounds are separate. -/
def Body (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ FuncType profile ft ∧
    BodyEncoding profile data ops ∧ MultiValue.FunctionTyped env locals ft ops ∧
    Instructions profile (functionContext env locals ft) ops

end Itasca.Profile
