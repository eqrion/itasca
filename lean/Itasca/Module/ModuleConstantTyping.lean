import Itasca.Module.ModuleConstants

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

/-- A decoded initializer denotes its single specification instruction. -/
def instruction : types.ConstExpr → instr
  | .I32 value => Core.i32Const value
  | .I64 value => ScalarConst.i64 value
  | .F32 bits => ScalarConst.f32 bits
  | .F64 bits => ScalarConst.f64 bits
  | .GlobalGet idx => .GLOBAL_GET (.mk_uN idx.val)

def expression (e : types.ConstExpr) : expr := [instruction e]

theorem instruction_wf (e : types.ConstExpr) : wf_instr (instruction e) := by
  cases e with
  | I32 value => exact Core.i32Const_wf value
  | I64 value => exact ScalarConst.i64_wf value
  | F32 value => exact ScalarConst.f32_wf value
  | F64 value => exact ScalarConst.f64_wf value
  | GlobalGet idx => exact .instr_case_46 _ (EnvTranslation.index_wf idx)

theorem expression_wf (e : types.ConstExpr) : Forall wf_instr (expression e) := by
  simpa [expression, Forall] using instruction_wf e

/-- Initializer contexts expose precisely the imported prefix of the global cache. -/
def GlobalContext (env : module.Env) (C : context) : Prop :=
  C.GLOBALS = (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType

private theorem global_lookup {env C} (hC : GlobalContext env C)
    (idx : U32) (gt : types.GlobalType) (hi : idx.val < env.global_types.val.length)
    (hgt : env.global_types.val[idx.val] = gt) (himport : idx.val < env.num_imported_globals.val) :
    idx.val < C.GLOBALS.length ∧ C.GLOBALS[idx.val]! = Translate.globalType gt := by
  rw [hC]
  have hb : idx.val < (env.global_types.val.take env.num_imported_globals.val).length := by simp; omega
  exact ⟨by simpa using hb, by
    rw [getElem!_pos _ _ (by simpa using hb), List.getElem_map, List.getElem_take, hgt]⟩

theorem Valid.instruction_typed {env e t} (h : Valid env e t)
    (C : context) (hC : wf_context C) (hglobals : GlobalContext env C) :
    Instr_ok C (instruction e) (.mk_functype (.mk_list []) (.mk_list [Translate.valueType t])) ∧
      Instr_const C (instruction e) := by
  cases h with
  | i32 value => exact ⟨Core.i32Const_typed C hC value, .const C _ _ hC (instruction_wf (.I32 value))⟩
  | i64 value => exact ⟨ScalarConst.i64_typed C hC value, .const C _ _ hC (instruction_wf (.I64 value))⟩
  | f32 value => exact ⟨ScalarConst.f32_typed C hC value, .const C _ _ hC (instruction_wf (.F32 value))⟩
  | f64 value => exact ⟨ScalarConst.f64_typed C hC value, .const C _ _ hC (instruction_wf (.F64 value))⟩
  | globalGet idx gt hi hgt himport hconst =>
    obtain ⟨hb, he⟩ := global_lookup hglobals idx gt hi hgt himport
    refine ⟨.global_get C _ _ (Translate.mutability gt.mutability) hb he hC (instruction_wf (.GlobalGet idx)), ?_⟩
    apply Instr_const.global_get C _ (Translate.valueType gt.valtype) hb _ hC
      (instruction_wf (.GlobalGet idx))
    simpa [Translate.globalType, hconst, Translate.mutability, proj_uN_0] using he

theorem Valid.expr_ok_const {env e t} (h : Valid env e t)
    (C : context) (hC : wf_context C) (hglobals : GlobalContext env C) :
    Expr_ok_const C (expression e) (Translate.valueType t) := by
  obtain ⟨ht, hc⟩ := h.instruction_typed C hC hglobals
  exact .mk_Expr_ok_const C _ _
    (.mk_Expr_ok C _ _ (.instr C _ [] _ ht hC (instruction_wf _)) hC (expression_wf _))
    (.mk_Expr_const C _ (by simpa [Forall, expression] using hc) hC (expression_wf _))
    hC (expression_wf _)

def global (g : module.Global) : _root_.global :=
  .GLOBAL (Translate.globalType g.gtype) (expression g.init)

theorem global_typed (env : module.Env) (g : module.Global)
    (h : Valid env g.init g.gtype.valtype) (C : context)
    (hC : wf_context C) (hglobals : GlobalContext env C) :
    Global_ok C (global g) (Translate.globalType g.gtype) := by
  apply Global_ok.mk_Global_ok C _ _ (Translate.mutability g.gtype.mutability)
      (Translate.valueType g.gtype.valtype)
  · exact Translate.globalType_valid _
  · rfl
  · exact h.expr_ok_const C hC hglobals
  · exact hC
  · exact .global_case_0 _ _ (expression_wf _)

end Itasca.ModuleConstants
