import Exec.Interp.Numeric.Float.FloatComparisonScalar
import Exec.Spec.FloatComparison

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

/-- Actual f32.eq dispatch takes the generated comparison step. -/
theorem scalar_f32_eq_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 91#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .EQ)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_eq ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .EQ)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_12 _ _ wf
  exact Spec.float_comparison_pure .F32 .EQ (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.ne dispatch takes the generated comparison step. -/
theorem scalar_f32_ne_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 92#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .NE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ne ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .NE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_14 _ _ wf
  exact Spec.float_comparison_pure .F32 .NE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.lt dispatch takes the generated comparison step. -/
theorem scalar_f32_lt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 93#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .LT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_lt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .LT)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_16 _ _ wf
  exact Spec.float_comparison_pure .F32 .LT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.gt dispatch takes the generated comparison step. -/
theorem scalar_f32_gt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 94#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .GT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_gt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .GT)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_18 _ _ wf
  exact Spec.float_comparison_pure .F32 .GT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.le dispatch takes the generated comparison step. -/
theorem scalar_f32_le_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 95#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .LE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_le ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .LE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_20 _ _ wf
  exact Spec.float_comparison_pure .F32 .LE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.ge dispatch takes the generated comparison step. -/
theorem scalar_f32_ge_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 96#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .GE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ge ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .GE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_22 _ _ wf
  exact Spec.float_comparison_pure .F32 .GE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f64.eq dispatch takes the generated comparison step. -/
theorem scalar_f64_eq_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 97#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .EQ)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_eq ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .EQ)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_13 _ _ wf
  exact Spec.float_comparison_pure .F64 .EQ (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.ne dispatch takes the generated comparison step. -/
theorem scalar_f64_ne_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 98#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .NE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ne ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .NE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_15 _ _ wf
  exact Spec.float_comparison_pure .F64 .NE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.lt dispatch takes the generated comparison step. -/
theorem scalar_f64_lt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 99#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .LT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_lt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .LT)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_17 _ _ wf
  exact Spec.float_comparison_pure .F64 .LT (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.gt dispatch takes the generated comparison step. -/
theorem scalar_f64_gt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 100#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .GT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_gt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .GT)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_19 _ _ wf
  exact Spec.float_comparison_pure .F64 .GT (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.le dispatch takes the generated comparison step. -/
theorem scalar_f64_le_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 101#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .LE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_le ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .LE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_21 _ _ wf
  exact Spec.float_comparison_pure .F64 .LE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.ge dispatch takes the generated comparison step. -/
theorem scalar_f64_ge_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 102#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .GE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ge ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .GE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_23 _ _ wf
  exact Spec.float_comparison_pure .F64 .GE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

end Itasca.Runtime.Interp
