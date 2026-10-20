import Exec.Interp.Simd.Float.SimdFloatResizeFirstLanes
import Exec.Interp.Simd.Float.SimdFloatResizeSound
import Exec.Spec.Choices.SimdFloatResizeFirst
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Platform

/-- Actual SIMD binary execution consumes the same source-only first-result
policy for every occurrence; lane selection is preserved by packing. -/
theorem float_resize_lanes_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (kind : Spec.Simd.FloatResize) (x : U128) :
    runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x ⦃ result =>
      ∃ value, result = .Ok value ∧ Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf (lanetype_Fnn kind.input)) (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.floatResizeSource kind) (.mk_uN x.val))
        (some (.mk_uN value.val)) ⦄ := by
  apply WP.spec_mono (float_resize_lanes_first floats laws kind x)
  rintro result ⟨value,rfl,first,zeroed⟩
  exact ⟨value,rfl,Spec.Simd.float_resize_chosen occurrence kind x.bv value.bv first zeroed⟩

theorem float_resize_simd_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (kind : Spec.Simd.FloatResize)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatResizeOpcode kind) offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Spec.ChosenVector Spec.firstVectorChoice occurrence
          (.convert (Spec.Simd.shapeOf (lanetype_Fnn kind.input)) (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.floatResizeSource kind) (.mk_uN x.val))
          (some (.mk_uN value.val)) ⦄ := by
  rw [float_resize_simd_eq]
  step with float_resize_lanes_chosen floats laws occurrence kind x as ⟨result,value,same,source⟩
  subst result
  exact ⟨value,rfl,source⟩
end Exec.Interp.Simd
