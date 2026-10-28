import Exec.Interp.Numeric.Float.FloatMinMax
import Exec.Spec.FloatMinMax

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

/-- Actual f32.min dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_min_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 150#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .MIN)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_min ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .MIN (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_min_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

/-- Actual f32.max dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_max_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 151#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .MAX)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_max ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .MAX (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_max_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

/-- Actual f64.min dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_min_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 164#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .MIN)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_min ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .MIN (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_min_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

/-- Actual f64.max dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_max_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 165#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .MAX)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_max ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .MAX (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_max_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

end Itasca.Runtime.Interp
