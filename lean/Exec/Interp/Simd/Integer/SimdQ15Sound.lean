import Exec.Interp.Simd.Integer.SimdQ15Packing
import Exec.Spec.SimdQ15Source
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem q15_lanes_sound (x y : U128)
    :
    runtime.interp.simd.multiply_lanes ((130#u32)) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf .I16) (Spec.Simd.q15Source)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (q15_lanes x y)
  intro result lanes
  exact Spec.Simd.q15_step x.bv y.bv result.bv
    (q15_packed x y result lanes)

theorem q15_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((130#u32)) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.multiply_lanes ((130#u32)) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem q15_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((130#u32)) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf .I16) (Spec.Simd.q15Source)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [q15_simd_eq floats offset laneIndex bits x y z memory]
  step with q15_lanes_sound x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd
