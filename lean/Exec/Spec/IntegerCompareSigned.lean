import Exec.Spec.IntegerSigned

namespace Exec.Spec

theorem integer_lts_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LT .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt < b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt < b.toInt)
  have boolean : nat_of_bool (decide (a.toInt < b.toInt)) = (if a.toInt < b.toInt then 1 else 0) := by
    by_cases h : a.toInt < b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_ilt_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt < b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_ilt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_4 .S _ _ _ relation wf
  · exact .fun_relop__case_5 .S _ _ _ relation wf

theorem integer_gts_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GT .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt > b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt > b.toInt)
  have boolean : nat_of_bool (decide (a.toInt > b.toInt)) = (if a.toInt > b.toInt then 1 else 0) := by
    by_cases h : a.toInt > b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_igt_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt > b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_igt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_6 .S _ _ _ relation wf
  · exact .fun_relop__case_7 .S _ _ _ relation wf

theorem integer_les_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LE .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt ≤ b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt ≤ b.toInt)
  have boolean : nat_of_bool (decide (a.toInt ≤ b.toInt)) = (if a.toInt ≤ b.toInt then 1 else 0) := by
    by_cases h : a.toInt ≤ b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_ile_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt ≤ b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_ile__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_8 .S _ _ _ relation wf
  · exact .fun_relop__case_9 .S _ _ _ relation wf

theorem integer_ges_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GE .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt ≥ b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt ≥ b.toInt)
  have boolean : nat_of_bool (decide (a.toInt ≥ b.toInt)) = (if a.toInt ≥ b.toInt then 1 else 0) := by
    by_cases h : a.toInt ≥ b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_ige_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt ≥ b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_ige__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_10 .S _ _ _ relation wf
  · exact .fun_relop__case_11 .S _ _ _ relation wf

end Exec.Spec
