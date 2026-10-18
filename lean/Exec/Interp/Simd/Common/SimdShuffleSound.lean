import Exec.Interp.Simd.Common.SimdShufflePacking
import Exec.Spec.SimdShuffle
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem shuffle_lanes_sound (bits x y : U128)
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32) :
    runtime.interp.simd.shuffle_lanes 13#u32 bits x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VSHUFFLE Spec.Simd.byteShape (Spec.Simd.byteWords bits.bv)] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shuffle_lanes 13#u32 bits x y)
  intro result lanes
  apply Spec.Simd.shuffle_step x.bv y.bv result.bv (Spec.Simd.byteWords bits.bv)
    (Spec.Simd.byteWords_length _) _ (shuffle_packed bits x y result bounded lanes)
  intro index member
  obtain ⟨j,valid,rfl⟩ := List.mem_map.mp member
  exact bounded j (List.mem_range.mp valid)

theorem shuffle_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 13#u32 offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.shuffle_lanes 13#u32 bits x y)
        (fun value => Result.ok (.Ok value,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem shuffle_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8))
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32) :
    runtime.interp.simd.simd floats 13#u32 offset laneIndex bits x y z memory ⦃ result =>
      ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VSHUFFLE Spec.Simd.byteShape (Spec.Simd.byteWords bits.bv)] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [shuffle_dispatch_eq]
  step with shuffle_lanes_sound as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Exec.Interp.Simd
