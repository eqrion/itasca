import Itasca.Runtime.Interp.Simd.Lanes.ShuffleBytes
import Itasca.Runtime.Spec.Simd.ByteSelect
import SpecExt.Builtins.LaneMap
import Itasca.Runtime.Spec.Simd.Shuffle

/-!
Shuffle packing and source dispatch, above the shared shuffle/swizzle byte loop.
-/

/-! ## Simd Shuffle Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shuffle_byte_source (bits x y : U128) (j : Nat)
    (bounded : Spec.Simd.byteAt bits.bv j < 32) :
    (shuffleByte 13#u32 bits x y j).toNat =
      proj_uN_0 ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[Spec.Simd.byteAt bits.bv j]!) := by
  change (selectedByte true x.bv y.bv (laneBits 8 j bits.bv).toNat).toNat = _
  rw [lane_bits_to_nat]
  change (selectedByte true x.bv y.bv (Spec.Simd.byteAt bits.bv j)).toNat = _
  rw [Spec.Simd.byte_words_append_get _ _ _ bounded]
  by_cases first : Spec.Simd.byteAt bits.bv j < 16
  · simp only [selectedByte,if_pos first]
    exact lane_bits_to_nat 8 _ x.bv
  · simp only [selectedByte,if_neg first,Bool.true_and,decide_eq_true_eq,if_pos bounded]
    exact lane_bits_to_nat 8 _ y.bv

theorem shuffle_packed (bits x y result : U128)
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32)
    (lanes : ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte 13#u32 bits x y j) :
    uN.mk_uN result.val = inv_lanes_ (Spec.Simd.shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8
        ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[
          proj_uN_0 (Spec.Simd.byteWords bits.bv)[k]!]!))) := by
  let values := fun (k : Nat) => proj_uN_0 ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[
    proj_uN_0 (Spec.Simd.byteWords bits.bv)[k]!]!)
  have selected (j : Nat) (valid : j < 16) :
      result.val / 2^(lsize lanetype.I8*j) % 2^lsize lanetype.I8 = values j := by
    change result.bv.toNat / 2^(8*j) % 2^8 = _
    rw [←lane_bits_to_nat,lanes j valid,shuffle_byte_source bits x y j (bounded j valid)]
    dsimp only [values]
    rw [Spec.Simd.byte_words_get bits.bv j valid]
    rfl
  have packed := SpecExt.Builtins.pack_map_of_lanes .I8 16 result.val values selected
  have valueBound : result.val < 2^(lsize lanetype.I8*16) := by
    change result.val < 2^128
    exact result.bv.isLt
  rw [Nat.mod_eq_of_lt valueBound] at packed
  change uN.mk_uN result.val = uN.mk_uN _
  apply congrArg uN.mk_uN
  rw [←packed]
  apply congrArg (SpecExt.Builtins.packLanes .I8)
  apply List.map_congr_left
  intro j member
  change lane_.mk_lane__0 .I8 (.mk_uN (values j)) = _
  dsimp only [values]
  congr 1

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shuffle Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem shuffle_lanes_sound (bits x y : U128)
    (bounded : ∀ j, j < 16 → Spec.Simd.byteAt bits.bv j < 32) :
    runtime.interp.simd.shuffle_lanes 13#u32 bits x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VSHUFFLE Spec.Simd.byteShape (Spec.Simd.byteWords bits.bv)] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shuffle_lanes 13#u32 bits x y)
  intro result lanes
  apply Spec.Simd.shuffle_step x.bv y.bv result.bv (Spec.Simd.byteWords bits.bv)
    (Spec.Simd.byte_words_length _) _ (shuffle_packed bits x y result bounded lanes)
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

end Itasca.Runtime.Interp.Simd

end
