import Itasca.Runtime.Interp.Simd.Lanes.ShuffleBytes
import Itasca.Runtime.Spec.Simd.Swizzle
import SpecExt.Builtins.LaneMap

/-!
Byte swizzle: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Swizzle Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem swizzle_byte_source (bits x y : U128) (j : Nat) :
    (shuffleByte 14#u32 bits x y j).toNat =
      proj_uN_0 ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv j]!) := by
  change (selectedByte false x.bv y.bv (laneBits 8 j y.bv).toNat).toNat = _
  rw [lane_bits_to_nat]
  change (selectedByte false x.bv y.bv (Spec.Simd.byteAt y.bv j)).toNat = _
  rw [Spec.Simd.swizzle_words_get _ _ (Spec.Simd.byte_at_bound _ _)]
  by_cases first : Spec.Simd.byteAt y.bv j < 16
  · simp only [selectedByte,if_pos first]
    exact lane_bits_to_nat 8 _ x.bv
  · simp [selectedByte,first,proj_uN_0]

theorem swizzle_packed (bits x y result : U128)
    (lanes : ∀ j, j < 16 → laneBits 8 j result.bv = shuffleByte 14#u32 bits x y j) :
    uN.mk_uN result.val = inv_lanes_ (Spec.Simd.shapeOf .I8)
      ((List.range 16).map (fun k => lane_.mk_lane__0 .I8
        ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv k]!))) := by
  let values := fun (k : Nat) => proj_uN_0 ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv k]!)
  have selected (j : Nat) (valid : j < 16) :
      result.val/2^(lsize lanetype.I8*j)%2^lsize lanetype.I8 = values j := by
    change result.bv.toNat/2^(8*j)%2^8 = _
    rw [←lane_bits_to_nat,lanes j valid,swizzle_byte_source]
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

/-! ## Simd Swizzle Sound -/

section

namespace Itasca.Runtime.Interp.Simd
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

end Itasca.Runtime.Interp.Simd

end
