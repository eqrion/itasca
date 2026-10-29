import Itasca.Runtime.Spec.Simd.Bitwise

/-!
The source relation and reduction step for any-true vector reduction.

Main declarations: `any_true_relation` and `any_true_step`. A direct consumer is `Interp.Simd.Bitwise.Whole`.
-/

namespace Itasca.Runtime.Spec.Simd

theorem any_true_relation (a : BitVec 128) :
    fun_ine_ 128 (.mk_uN a.toNat) (.mk_uN 0)
      (.mk_uN (if a.toNat ≠ 0 then 1 else 0)) := by
  have hbool : nat_of_bool (uN.mk_uN a.toNat != uN.mk_uN 0) =
      (if a.toNat ≠ 0 then 1 else 0) := by
    change nat_of_bool (a.toNat != 0) = _
    by_cases h : a.toNat = 0
    · simp [h, bne, nat_of_bool]
    · have hb : (a.toNat == 0) = false := beq_eq_false_iff_ne.mpr h
      simp [bne, hb, h, nat_of_bool]
  rw [←hbool]
  exact .fun_ine__case_0 _ _ _ (boolean_u32_wf _)

theorem any_true_step (a : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VVTESTOP .V128 .ANY_TRUE]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (if a.toNat ≠ 0 then 1 else 0)))] := by
  exact .vvtestop _ _ _ (by decide) (any_true_relation a) (by simp [proj_num__0]) rfl
    (predicate_i32_wf _) (const_wf a) (.admininstr_case_24 ..)
    (.admininstr_case_13 _ _ (predicate_i32_wf _))
    (unsigned_wf_of_lt 128 0 (by decide))

end Itasca.Runtime.Spec.Simd
