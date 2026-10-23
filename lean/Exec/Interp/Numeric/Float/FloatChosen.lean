import Exec.Interp.Numeric.Float.FloatFirstChoice
import Exec.Spec.NumericPolicyMatching
/-! Actual scalar arithmetic kernels consume a fixed source numeric policy.
The agreement follows from FloatOpsCorrect and checked NaN canonicalization. -/
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f32_ceil_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 141#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F32 (.mk_unop__1 .F32 .CEIL) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_ceil_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F32 .CEIL _ _ _
    (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_ceil_relation _  (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_floor_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 142#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_floor_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F32 .FLOOR _ _ _
    (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_floor_relation _  (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_trunc_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 143#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_trunc_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F32 .TRUNC _ _ _
    (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_trunc_relation _  (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_nearest_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 144#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_nearest_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F32 .NEAREST _ _ _
    (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_nearest_relation _  (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_sqrt_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 145#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F32 (.mk_unop__1 .F32 .SQRT) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_sqrt_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F32 .SQRT _ _ _
    (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_sqrt_relation _  (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_add_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 146#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F32 (.mk_binop__1 .F32 .ADD) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_add_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F32 .ADD _ _ _ _
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_add_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_sub_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 147#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F32 (.mk_binop__1 .F32 .SUB) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_sub_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F32 .SUB _ _ _ _
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_sub_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_mul_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 148#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F32 (.mk_binop__1 .F32 .MUL) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_mul_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F32 .MUL _ _ _ _
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_mul_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_div_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 149#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F32 (.mk_binop__1 .F32 .DIV) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_div_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F32 .DIV _ _ _ _
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) (Spec.float_f32_div_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f64_ceil_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 155#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F64 (.mk_unop__1 .F64 .CEIL) (.mk_num__1 .F64 (floatOfBits 64 a.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_ceil_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F64 .CEIL _ _ _
    (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_ceil_relation _  (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_floor_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 156#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_num__1 .F64 (floatOfBits 64 a.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_floor_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F64 .FLOOR _ _ _
    (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_floor_relation _  (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_trunc_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 157#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_num__1 .F64 (floatOfBits 64 a.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_trunc_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F64 .TRUNC _ _ _
    (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_trunc_relation _  (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_nearest_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 158#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_num__1 .F64 (floatOfBits 64 a.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_nearest_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F64 .NEAREST _ _ _
    (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_nearest_relation _  (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_sqrt_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 159#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.unary .F64 (.mk_unop__1 .F64 .SQRT) (.mk_num__1 .F64 (floatOfBits 64 a.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_sqrt_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_unary_first occurrence .F64 .SQRT _ _ _
    (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_sqrt_relation _  (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_add_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 160#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F64 (.mk_binop__1 .F64 .ADD) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_add_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F64 .ADD _ _ _ _
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_add_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_sub_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 161#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F64 (.mk_binop__1 .F64 .SUB) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_sub_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F64 .SUB _ _ _ _
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_sub_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_mul_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 162#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F64 (.mk_binop__1 .F64 .MUL) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_mul_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F64 .MUL _ _ _ _
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_mul_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_div_chosen {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 163#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence
        (.binary .F64 (.mk_binop__1 .F64 .DIV) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_div_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F64 .DIV _ _ _ _
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) (Spec.float_f64_div_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head
end Exec.Interp
