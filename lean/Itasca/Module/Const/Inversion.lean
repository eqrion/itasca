import Itasca.Module.Elab.TypingInversion

/-!
# Inversion of constant expression typing

Recovers `ModuleConstants.Valid` from generated typing. `valid_of_typing` shows that a constant
initializer typed by `Expr_ok_const` is valid in the environment, including that `global.get`
targets an imported immutable global. Used by the completeness proofs for globals and segments.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleConstants

/-- A constant, well-typed initializer instruction is valid at some type. -/
theorem constant_valid_type {env : module.Env} {C : context} {e : types.ConstExpr}
    (hg : GlobalContext env C) (hf : FunctionContext env C)
    (h : Instr_const C (instruction e))
    {ins outs : List valtype}
    (ht : Instr_ok C (instruction e) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ∃ ty, Valid env e ty := by
  change C.GLOBALS = (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType at hg
  change C.FUNCS = env.func_types.val.map EnvTranslation.funcType at hf
  cases e with
  | I32 value => exact ⟨.I32, .i32 value⟩
  | I64 value => exact ⟨.I64, .i64 value⟩
  | F32 bits => exact ⟨.F32, .f32 bits⟩
  | F64 bits => exact ⟨.F64, .f64 bits⟩
  | V128 low high => exact ⟨.V128, .v128 low high⟩
  | RefNull ty => exact ⟨referenceValueType ty, .refNull ty⟩
  | RefFunc idx =>
    cases ht with
    | ref_func _ _ _ hi _ _ _ =>
      exact ⟨.FuncRef, .refFunc idx (by simpa [hf, proj_uN_0] using hi)⟩
  | GlobalGet idx =>
    cases h with
    | global_get _ t hi he hw hf =>
      have hbound : idx.val < (env.global_types.val.take env.num_imported_globals.val).length := by
        simpa [hg, proj_uN_0] using hi
      have hi' : idx.val < env.global_types.val.length := by simp only [List.length_take] at hbound; omega
      have hn : idx.val < env.num_imported_globals.val := by simp only [List.length_take] at hbound; omega
      let gt := env.global_types.val[idx.val]
      have hgt : Translate.globalType gt = .mk_globaltype none t := by
        change C.GLOBALS[idx.val]! = .mk_globaltype none t at he
        rw [hg, getElem!_pos _ _ (by simpa using hbound), List.getElem_map, List.getElem_take] at he
        exact he
      have hm : gt.mutability = .Const := by
        apply Translate.mutability_injective
        exact (globaltype.mk_globaltype.inj hgt).1
      exact ⟨gt.valtype, .globalGet idx gt hi' rfl hn hm⟩

/-- The output type of a typed initializer instruction is unique. -/
theorem instruction_output_unique {C : context} {e : types.ConstExpr} {ins outs ins' outs'}
    (h : Instr_ok C (instruction e) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (h' : Instr_ok C (instruction e) (.mk_functype (.mk_list ins') (.mk_list outs'))) :
    outs = outs' := by
  cases e <;> cases h <;> cases h' <;> simp_all

/-- An initializer typed by `Expr_ok_const` at `Translate.valueType ty` satisfies `Valid env e
ty`. -/
theorem valid_of_typing {env : module.Env} {C : context} {e : types.ConstExpr} {ty : types.ValueType}
    (hg : GlobalContext env C) (hfunctions : FunctionContext env C) (h : Expr_ok_const C (expression e) (Translate.valueType ty)) :
    Valid env e ty := by
  cases h with
  | mk_Expr_ok_const ht hc hw hws =>
    have hconst : Instr_const C (instruction e) := by
      cases hc with
      | mk_Expr_const hc _ _ => exact hc _ (by simp [expression])
    have hseq : Instrs_ok C (expression e)
        (.mk_functype (.mk_list []) (.mk_list [Translate.valueType ty])) := by cases ht; assumption
    obtain ⟨front, ins, outs, hp, hi, ho⟩ := DeclarativeComplete.singleton hseq
    obtain ⟨actual, hv⟩ := constant_valid_type hg hfunctions hconst hp
    have hcanonical := (hv.instruction_typed C hw hg hfunctions).1
    have hn := DeclarativeComplete.result_sub_length hi
    have hf : front = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_nil, List.length_append] at hn
      omega
    have hout := instruction_output_unique hp hcanonical
    rw [hf, List.nil_append, hout] at ho
    have hs := DeclarativeComplete.result_sub_iff.mp ho
    have hsv : Valtype_sub (Translate.valueType actual) (Translate.valueType ty) := (List.forall₂_cons.mp hs).1
    have hnot : Translate.valueType actual ≠ .BOT := by cases actual <;> decide
    have sub_eq : ∀ {a b : valtype}, a ≠ .BOT → Valtype_sub a b → a = b := by
      intro a b hn ht
      cases ht with
      | refl => rfl
      | bot => exact False.elim (hn rfl)
    have he := Translate.valueType_injective (sub_eq hnot hsv)
    simpa [he] using hv

end Itasca.ModuleConstants
