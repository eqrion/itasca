import Itasca.Binary.Module
import Itasca.Module.Elab.Translation

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

/-- The operand type corresponding to a table/reference type. -/
def referenceValueType : types.ElemType → types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

/-- Initializer validity is independent of parser execution. A `ref.func`
initializer declares its own reference; index bounds still have to hold. -/
inductive Valid (env : module.Env) : types.ConstExpr → types.ValueType → Prop where
  | i32 (value : I32) : Valid env (.I32 value) .I32
  | i64 (value : I64) : Valid env (.I64 value) .I64
  | f32 (value : U32) : Valid env (.F32 value) .F32
  | f64 (value : U64) : Valid env (.F64 value) .F64
  | v128 (low high : U64) : Valid env (.V128 low high) .V128
  | refNull (ty : types.ElemType) : Valid env (.RefNull ty) (referenceValueType ty)
  | refFunc (idx : U32) (hi : idx.val < env.func_types.val.length) :
      Valid env (.RefFunc idx) .FuncRef
  | globalGet (idx : U32) (gt : types.GlobalType)
      (hi : idx.val < env.global_types.val.length)
      (hgt : env.global_types.val[idx.val] = gt)
      (himport : idx.val < env.num_imported_globals.val)
      (hconst : gt.mutability = .Const) : Valid env (.GlobalGet idx) gt.valtype

/-- A well-typed initializer cannot introduce a disallowed constant form when
its expected operand type is admitted by the selected profile. -/
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

/-- Initializer syntax preserves the low-to-high order of all vector bits. -/
def instruction : types.ConstExpr → instr
  | .I32 value => Spec.i32Const value
  | .I64 value => ScalarConst.i64 value
  | .F32 bits => ScalarConst.f32 bits
  | .F64 bits => ScalarConst.f64 bits
  | .V128 low high => .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))
  | .RefNull ty => .REF_NULL (Translate.referenceType ty)
  | .RefFunc idx => .REF_FUNC (.mk_uN idx.val)
  | .GlobalGet idx => .GLOBAL_GET (.mk_uN idx.val)

def expression (e : types.ConstExpr) : expr := [instruction e]

theorem instruction_wf (e : types.ConstExpr) : wf_instr (instruction e) := by
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

theorem expression_wf (e : types.ConstExpr) : Forall wf_instr (expression e) := by
  simpa [expression, Forall] using instruction_wf e

/-- Initializers expose the imported prefix of the global cache. -/
def GlobalContext (env : module.Env) (C : context) : Prop :=
  C.GLOBALS = (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType

/-- Function reference bounds use the complete imported-and-defined function space. -/
def FunctionContext (env : module.Env) (C : context) : Prop :=
  C.FUNCS = env.func_types.val.map EnvTranslation.funcType

end Itasca.ModuleConstants
