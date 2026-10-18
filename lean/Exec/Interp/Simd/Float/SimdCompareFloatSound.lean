import Exec.Interp.Simd.Float.SimdCompareFloatPacking
import Exec.Spec.SimdCompareFloatStep
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem float_compare_lanes_sound (ty : Fnn) (op : vrelop_Fnn_N) (x y : U128)
    :
    runtime.interp.simd.compare_lanes (floatCompareOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VRELOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatCompareSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_compare_lanes ty op x y)
  intro result lanes
  exact Spec.Simd.float_comparison_step ty op x.bv y.bv result.bv
    (float_compare_packed ty op x y result lanes)

theorem float_compare_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vrelop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatCompareOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.compare_lanes (floatCompareOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.simd floatCompareOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_compare_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vrelop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatCompareOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VRELOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatCompareSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_compare_simd_eq]
  step with float_compare_lanes_sound ty op x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Exec.Interp.Simd
