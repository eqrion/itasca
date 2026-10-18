import Exec.Spec.Wf

/-! Generated integer comparison relations. The input integers are interpreted
at their declared width by the caller; comparisons always return an i32 Boolean. -/

namespace Exec.Spec

theorem boolean_u32_wf (answer : Bool) :
    wf_uN 32 (.mk_uN (nat_of_bool answer)) := by
  cases answer <;> apply wf_uN.uN_case_0 <;> decide

theorem predicate_u32_wf (answer : Prop) [Decidable answer] :
    wf_uN 32 (.mk_uN (if answer then 1 else 0)) := by
  by_cases h : answer <;> simp only [h, if_true, if_false]
  all_goals apply wf_uN.uN_case_0; decide

theorem predicate_i32_wf (answer : Prop) [Decidable answer] :
    wf_num_ .I32 (.mk_num__0 .I32 (.mk_uN (if answer then 1 else 0))) := by
  exact .num__case_0 _ _ _ (by decide) (predicate_u32_wf answer) rfl

/-- EQ returns exactly the Boolean specified by the generated rule. -/
theorem integer_eq_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty .EQ)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a = b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a = b)
  have hbool : nat_of_bool (uN.mk_uN a == uN.mk_uN b) = (if a = b then 1 else 0) := by
    change nat_of_bool (a == b) = _
    by_cases h : a = b
    · subst b; simp [nat_of_bool]
    · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
      simp [hb, h, nat_of_bool]
  have hi : fun_ieq_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a = b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ieq_.fun_ieq__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_0 _ _ _ hi hn
  | I64 => exact .fun_relop__case_1 _ _ _ hi hn

/-- NE returns exactly the Boolean specified by the generated rule. -/
theorem integer_ne_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty .NE)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a ≠ b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a ≠ b)
  have hbool : nat_of_bool (uN.mk_uN a != uN.mk_uN b) = (if a ≠ b then 1 else 0) := by
    change nat_of_bool (a != b) = _
    by_cases h : a = b
    · subst b; simp [bne, nat_of_bool]
    · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
      simp [bne, hb, h, nat_of_bool]
  have hi : fun_ine_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a ≠ b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ine_.fun_ine__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_2 _ _ _ hi hn
  | I64 => exact .fun_relop__case_3 _ _ _ hi hn

/-- LTU returns exactly the Boolean specified by the generated rule. -/
theorem integer_ltu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LT .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a < b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a < b)
  have hbool : nat_of_bool (decide (a < b)) = (if a < b then 1 else 0) := by
    change nat_of_bool (decide (a < b)) = _
    by_cases h : a < b <;> simp [h, nat_of_bool]
  have hi : fun_ilt_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a < b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ilt_.fun_ilt__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_4 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_5 .U _ _ _ hi hn

/-- GTU returns exactly the Boolean specified by the generated rule. -/
theorem integer_gtu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GT .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a > b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a > b)
  have hbool : nat_of_bool (decide (a > b)) = (if a > b then 1 else 0) := by
    change nat_of_bool (decide (a > b)) = _
    by_cases h : a > b <;> simp [h, nat_of_bool]
  have hi : fun_igt_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a > b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_igt_.fun_igt__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_6 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_7 .U _ _ _ hi hn

/-- LEU returns exactly the Boolean specified by the generated rule. -/
theorem integer_leu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LE .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a ≤ b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a ≤ b)
  have hbool : nat_of_bool (decide (a ≤ b)) = (if a ≤ b then 1 else 0) := by
    change nat_of_bool (decide (a ≤ b)) = _
    by_cases h : a ≤ b <;> simp [h, nat_of_bool]
  have hi : fun_ile_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a ≤ b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ile_.fun_ile__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_8 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_9 .U _ _ _ hi hn

/-- GEU returns exactly the Boolean specified by the generated rule. -/
theorem integer_geu_relation (ty : Inn) (a b : Nat) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GE .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN (if a ≥ b then 1 else 0)))) := by
  have hn := predicate_i32_wf (a ≥ b)
  have hbool : nat_of_bool (decide (a ≥ b)) = (if a ≥ b then 1 else 0) := by
    change nat_of_bool (decide (a ≥ b)) = _
    by_cases h : a ≥ b <;> simp [h, nat_of_bool]
  have hi : fun_ige_ (sizenn (numtype_Inn ty)) .U (.mk_uN a) (.mk_uN b)
      (.mk_uN (if a ≥ b then 1 else 0)) := by
    rw [← hbool]
    exact (fun_ige_.fun_ige__case_0 (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b) (boolean_u32_wf _))
  cases ty with
  | I32 => exact .fun_relop__case_10 .U _ _ _ hi hn
  | I64 => exact .fun_relop__case_11 .U _ _ _ hi hn

end Exec.Spec
