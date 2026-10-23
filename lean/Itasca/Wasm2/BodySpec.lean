import Itasca.Binary.Wasm2.Encoding
import Itasca.Binary.Wasm2.DeclaredReferences
import Itasca.Wasm1.ProfileSyntax

/-!
# Wasm 2.0 body contract

The contract that the body validator is proved against, stated without reference to the
validator. `Validated` says that a body is a binary-grammar instruction sequence (`BodyEncoding`),
is typed by the generated `Instrs_ok` rules (`FunctionTyped`), and satisfies the
declared-function-reference condition. For Wasm 1.0 the same instructions also follow the Wasm 1.0
grammar and `Wasm1.Instructions`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The typing context of a function body. Return typing comes from the selected type-section
entry. The runtime's shared scalar context carries empty results because `return` is dispatched by
the Wasm 2.0 body loop itself. Function parameters are already included in locals. -/
def bodyContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context := EnvTranslation.context env ⟨locals, ft.results⟩

/-- The context of a function body: the function label on top of `bodyContext`. -/
def functionContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context :=
  Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft

/-- The instruction sequence is typed by the generated `Instrs_ok` rules from no operands to the
function's result type, with the function label in scope. -/
def FunctionTyped (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) (ops : List instr) : Prop :=
  Instrs_ok (functionContext env locals ft)
    ops (.mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translate.valueType)))

/-- The whole-body certificate used by both soundness and completeness. It contains no
validator-success premise and imposes no Wasm 1.0 result-arity restriction. -/
def Validated (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ BodyEncoding data ops ∧
    FunctionTyped env locals ft ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops ∧
    (profile = .Wasm1 → Wasm1.BodyEncoding data ops ∧
      Wasm1.Instructions (functionContext env locals ft) ops)

end Itasca.Wasm2
