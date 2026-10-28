import Exec.Interp.Numeric.Float.FloatInstructionOutcome
import Exec.Interp.Numeric.Float.FloatComparisonBounded
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f32_eq_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .EQ)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .EQ) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_eq_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_ne_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .NE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .NE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_ne_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_lt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .LT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .LT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_lt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_gt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .GT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .GT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_gt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_le_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .LE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .LE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_le_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_ge_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .GE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .GE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_ge_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_eq_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .EQ)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .EQ) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_eq_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_ne_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .NE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .NE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ne_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_lt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .LT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .LT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_lt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_gt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .GT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .GT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_gt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_le_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .LE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .LE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_le_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_ge_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .GE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .GE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ge_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_reinterpret_i32_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I32)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretInt .I32) a b result ⦄ := by
  have run : runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I32)) a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · change (UScalar.cast .U64 (UScalar.cast .U32 a)).val < 2^32
    scalar_tac
  · have source := Spec.f32_reinterpret_i32_pure (UScalar.cast .U32 a).val (by scalar_tac)
    simp only [U32.cast_U64_val_eq]
    exact source

theorem scalar_i32_reinterpret_f32_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F32)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretFloat .F32) a b result ⦄ := by
  have run : runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F32)) a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · change (UScalar.cast .U64 (UScalar.cast .U32 a)).val < 2^32
    scalar_tac
  · have source := Spec.i32_reinterpret_f32_pure (UScalar.cast .U32 a).val (by scalar_tac)
    simp only [U32.cast_U64_val_eq]
    exact source

end Itasca.Runtime.Interp
