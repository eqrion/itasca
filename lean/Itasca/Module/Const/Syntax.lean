import Itasca.Binary.Module
import Itasca.Module.Elab.Translation

/-!
# Constant expression syntax

`ModuleConstants.Valid` is the validator's typing relation for constant initializers
(`wasm_types.ConstExpr`), independent of parsing. `instruction` and `expression` translate an
initializer to SpecTec syntax, and `GlobalContext` and `FunctionContext` tie a SpecTec `context`
to the decoded environment. Typing against `Expr_ok_const` is in `Module/Const/Typing`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

/-- The operand type corresponding to a table element type. -/
def referenceValueType : wasm_types.ElemType → wasm_types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

/-- The initializer has the given type in `env`. `ref.func` needs an in-range function index, and
`global.get` needs an imported immutable global. -/
inductive Valid (env : metadata.Env) : wasm_types.ConstExpr → wasm_types.ValueType → Prop where
  | i32 (value : I32) : Valid env (.I32 value) .I32
  | i64 (value : I64) : Valid env (.I64 value) .I64
  | f32 (value : U32) : Valid env (.F32 value) .F32
  | f64 (value : U64) : Valid env (.F64 value) .F64
  | v128 (low high : U64) : Valid env (.V128 low high) .V128
  | refNull (ty : wasm_types.ElemType) : Valid env (.RefNull ty) (referenceValueType ty)
  | refFunc (idx : U32) (hi : idx.val < env.func_types.val.length) :
      Valid env (.RefFunc idx) .FuncRef
  | globalGet (idx : U32) (gt : wasm_types.GlobalType)
      (hi : idx.val < env.global_types.val.length)
      (hgt : env.global_types.val[idx.val] = gt)
      (himport : idx.val < env.num_imported_globals.val)
      (hconst : gt.mutability = .Const) : Valid env (.GlobalGet idx) gt.valtype

/-- A valid initializer uses only constant forms the profile allows, when its type is allowed. -/
theorem Valid.const_allowed {env value expected} (h : Valid env value expected)
    {profile : ValidationProfile} (ha : ModuleBinary.ValueTypeAllowed profile expected) :
    ModuleBinary.ConstAllowed profile value := by
  cases h with
  | i32 _ | i64 _ | f32 _ | f64 _ | globalGet => cases profile <;> trivial
  | v128 _ _ | refFunc =>
    cases profile <;> simp_all [ModuleBinary.ValueTypeAllowed, ModuleBinary.ConstAllowed]
  | refNull ty =>
    cases profile <;> cases ty <;>
      simp_all [ModuleBinary.ValueTypeAllowed, ModuleBinary.ConstAllowed, referenceValueType]

/-- Translates an initializer to a SpecTec instruction. `V128` combines the low and high halves in
little-endian order. -/
def instruction : wasm_types.ConstExpr → instr
  | .I32 value => Spec.i32Const value
  | .I64 value => ScalarConst.i64 value
  | .F32 bits => ScalarConst.f32 bits
  | .F64 bits => ScalarConst.f64 bits
  | .V128 low high => .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))
  | .RefNull ty => .REF_NULL (Translate.referenceType ty)
  | .RefFunc idx => .REF_FUNC (.mk_uN idx.val)
  | .GlobalGet idx => .GLOBAL_GET (.mk_uN idx.val)

/-- The single-instruction SpecTec expression of an initializer. -/
def expression (e : wasm_types.ConstExpr) : expr := [instruction e]

/-- The translated instruction is well-formed. -/
theorem instruction_wf (e : wasm_types.ConstExpr) : wf_instr (instruction e) := by
  cases e with
  | I32 value => exact Spec.i32Const_wf value
  | I64 value => exact ScalarConst.i64_wf value
  | F32 value => exact ScalarConst.f32_wf value
  | F64 value => exact ScalarConst.f64_wf value
  | V128 low high =>
    apply wf_instr.instr_case_20
    · decide
    · constructor
      have hlo : low.val ≤ 18446744073709551615 := by scalar_tac
      have hhi : high.val ≤ 18446744073709551615 := by scalar_tac
      norm_num [size, valtype_vectype]
      omega
  | RefNull _ => exact .instr_case_40 _
  | RefFunc idx => exact .instr_case_41 _ (EnvTranslation.index_wf idx)
  | GlobalGet idx => exact .instr_case_46 _ (EnvTranslation.index_wf idx)

theorem expression_wf (e : wasm_types.ConstExpr) : Forall wf_instr (expression e) := by
  simpa [expression, Forall] using instruction_wf e

/-- `C.GLOBALS` is the imported prefix of the environment's global types. -/
def GlobalContext (env : metadata.Env) (C : context) : Prop :=
  C.GLOBALS = (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType

/-- `C.FUNCS` is the environment's function types, imported and defined. -/
def FunctionContext (env : metadata.Env) (C : context) : Prop :=
  C.FUNCS = env.func_types.val.map EnvTranslation.funcType

end Itasca.ModuleConstants
