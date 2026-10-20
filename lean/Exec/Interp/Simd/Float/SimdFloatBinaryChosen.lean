import Exec.Interp.Simd.Float.SimdFloatBinaryFirstLanes
import Exec.Interp.Simd.Float.SimdFloatBinarySound
import Exec.Spec.Choices.SimdFloatBinaryFirst
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Platform

/-- Actual SIMD binary execution consumes the same source-only first-result
policy for every occurrence; lane selection is preserved by packing. -/
theorem float_binary_lanes_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y ⦃ result =>
      Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.binary (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op) (.mk_uN x.val) (.mk_uN y.val))
        (some (.mk_uN result.val)) ⦄ := by
  apply WP.spec_mono (float_binary_lanes_first floats laws ty op x y)
  intro result first
  exact Spec.Simd.float_binary_chosen occurrence ty op x.bv y.bv result.bv first

theorem float_binary_simd_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (ty : Fnn) (op : vbinop_Fnn_N)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatBinaryOpcode ty op) offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Spec.ChosenVector Spec.firstVectorChoice occurrence
          (.binary (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op) (.mk_uN x.val) (.mk_uN y.val))
          (some (.mk_uN value.val)) ⦄ := by
  rw [float_binary_simd_eq]
  step with float_binary_lanes_chosen floats laws occurrence ty op x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Exec.Interp.Simd
