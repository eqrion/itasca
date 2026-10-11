import Itasca.MultiValue.Binary

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Return typing comes from the selected type-section entry. The runtime's
shared scalar context carries empty results because return is dispatched by
the multi-value loop itself. Function parameters are already included in locals. -/
def bodyContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context := EnvTranslation.context env ⟨locals, ft.results⟩

def FunctionTyped (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) (ops : List instr) : Prop :=
  Instrs_ok (Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft)
    ops (.mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translate.valueType)))

/-- Intended whole-body soundness/completeness certificate. It contains no
validator-success premise and imposes no Wasm 1.0 result-arity restriction. -/
def Validated (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ BodyEncoding data ops ∧
    FunctionTyped env locals ft ops

end Itasca.MultiValue
