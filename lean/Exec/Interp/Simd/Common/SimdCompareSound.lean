import Exec.Interp.Simd.Common.SimdComparePacking
import Exec.Spec.SimdCompareStep
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_compare_lanes_sound (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VRELOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerCompareSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_compare_lanes ty op x y supported)
  intro result lanes
  rw [integerCompareWidth_val] at lanes
  exact Spec.Simd.integer_comparison_step ty op x.bv y.bv result.bv supported
    (integer_compare_packed ty op x y result lanes)

theorem integer_compare_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : vrelop_Jnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (integerCompareOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op <;> (try rename_i sign; cases sign)
  all_goals unfold runtime.interp.simd.simd integerCompareOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_compare_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : vrelop_Jnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.simd floats (integerCompareOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VRELOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerCompareSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_compare_simd_eq]
  step with integer_compare_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Exec.Interp.Simd
