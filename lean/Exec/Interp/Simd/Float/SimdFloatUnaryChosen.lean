import Exec.Interp.Simd.Float.SimdFloatUnaryFirstLanes
import Exec.Interp.Simd.Float.SimdFloatUnarySound
import Exec.Spec.Choices.SimdFloatUnaryFirst
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Platform

/-- Actual SIMD unary execution consumes the same source-only first-result
policy for every occurrence; lane selection is preserved by packing. -/
theorem float_unary_lanes_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x ⦃ result =>
      Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.unary (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op) (.mk_uN x.val))
        (some (.mk_uN result.val)) ⦄ := by
  apply WP.spec_mono (float_unary_lanes_first floats laws ty op x)
  intro result first
  exact Spec.Simd.float_unary_chosen occurrence ty op x.bv result.bv first

theorem float_unary_simd_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (ty : Fnn) (op : vunop_Fnn_N)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatUnaryOpcode ty op) offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Spec.ChosenVector Spec.firstVectorChoice occurrence
          (.unary (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op) (.mk_uN x.val))
          (some (.mk_uN value.val)) ⦄ := by
  rw [float_unary_simd_eq]
  step with float_unary_lanes_chosen floats laws occurrence ty op x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Exec.Interp.Simd
