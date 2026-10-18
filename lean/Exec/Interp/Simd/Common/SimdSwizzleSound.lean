import Exec.Interp.Simd.Common.SimdSwizzlePacking
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem swizzle_lanes_sound (bits x y : U128) :
    runtime.interp.simd.shuffle_lanes 14#u32 bits x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VSWIZZLE Spec.Simd.byteShape] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shuffle_lanes 14#u32 bits x y)
  intro result lanes
  exact Spec.Simd.swizzle_step x.bv y.bv result.bv (swizzle_packed bits x y result lanes)

theorem swizzle_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 14#u32 offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.shuffle_lanes 14#u32 bits x y)
        (fun value => Result.ok (.Ok value,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem swizzle_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 14#u32 offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VSWIZZLE Spec.Simd.byteShape] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [swizzle_dispatch_eq]
  step with swizzle_lanes_sound as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Exec.Interp.Simd
