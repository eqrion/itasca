import Exec.Interp.Numeric.Float.FloatMinMaxFirst
import Exec.Spec.NumericPolicyMatching
import Exec.Spec.FloatMinMax
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem binary32_min_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U32) :
    runtime.interp.float.binary32 ops 4#u16 a b ⦃ result =>
      Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F32 (.mk_binop__1 .F32 .MIN) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (.mk_num__1 .F32 (floatOfBits 32 b.val))) (some (.mk_num__1 .F32 (floatOfBits 32 result.val))) ⦄ := by
  apply WP.spec_mono (binary32_min_first_choice ops a b)
  intro result head
  exact Spec.chosen_float_binary_first occurrence .F32 .MIN _ _ _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
    (Spec.float_f32_min_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_min_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 150#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F32 (.mk_binop__1 .F32 .MIN) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_min_first_choice ops a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F32 .MIN _ _ _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
    (Spec.float_f32_min_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem binary32_max_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U32) :
    runtime.interp.float.binary32 ops 5#u16 a b ⦃ result =>
      Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F32 (.mk_binop__1 .F32 .MAX) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (.mk_num__1 .F32 (floatOfBits 32 b.val))) (some (.mk_num__1 .F32 (floatOfBits 32 result.val))) ⦄ := by
  apply WP.spec_mono (binary32_max_first_choice ops a b)
  intro result head
  exact Spec.chosen_float_binary_first occurrence .F32 .MAX _ _ _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
    (Spec.float_f32_max_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem scalar_f32_max_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 151#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F32 (.mk_binop__1 .F32 .MAX) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))) (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_max_first_choice ops a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F32 .MAX _ _ _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
    (Spec.float_f32_max_relation _ _ (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)) head

theorem binary64_min_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.binary64 ops 4#u16 a b ⦃ result =>
      Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F64 (.mk_binop__1 .F64 .MIN) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 result.val))) ⦄ := by
  apply WP.spec_mono (binary64_min_first_choice ops a b)
  intro result head
  exact Spec.chosen_float_binary_first occurrence .F64 .MIN _ _ _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
    (Spec.float_f64_min_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_min_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 164#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F64 (.mk_binop__1 .F64 .MIN) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_min_first_choice ops a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F64 .MIN _ _ _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
    (Spec.float_f64_min_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head

theorem binary64_max_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.binary64 ops 5#u16 a b ⦃ result =>
      Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F64 (.mk_binop__1 .F64 .MAX) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 result.val))) ⦄ := by
  apply WP.spec_mono (binary64_max_first_choice ops a b)
  intro result head
  exact Spec.chosen_float_binary_first occurrence .F64 .MAX _ _ _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
    (Spec.float_f64_max_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head

theorem scalar_f64_max_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 165#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ Spec.ChosenNumeric Spec.firstNumericChoice occurrence (.binary .F64 (.mk_binop__1 .F64 .MAX) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))) (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_max_first_choice ops a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  exact Spec.chosen_float_binary_first occurrence .F64 .MAX _ _ _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
    (Spec.float_f64_max_relation _ _ (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)) head
end Exec.Interp
