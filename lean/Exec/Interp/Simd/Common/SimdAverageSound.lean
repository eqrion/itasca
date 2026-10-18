import Exec.Interp.Simd.Common.SimdAveragePacking
import Exec.Spec.SimdAverage
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem average_lanes_sound (ty : Jnn) (x y : U128)
    (supported : Spec.Simd.averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.averageSource ty)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (average_lanes ty x y supported)
  intro result lanes
  exact Spec.Simd.average_step ty x.bv y.bv result.bv supported
    (average_packed ty x y result lanes)

theorem average_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.averageSupported ty) :
    runtime.interp.simd.simd floats (averageOpcode ty) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty
  all_goals simp only [Spec.Simd.averageSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.simd averageOpcode
  all_goals with_unfolding_all rfl

@[step] theorem average_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.averageSupported ty) :
    runtime.interp.simd.simd floats (averageOpcode ty) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.averageSource ty)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [average_simd_eq floats ty offset laneIndex bits x y z memory supported]
  step with average_lanes_sound ty x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Exec.Interp.Simd
