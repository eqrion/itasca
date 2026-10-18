import Exec.Interp.Simd.Common.SimdShuffleLoop
import Exec.Spec.SimdSwizzle
import SpecExt.Builtins.LaneMap
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

theorem swizzle_byte_source (bits x y : U128) (j : Nat) :
    (shuffleByte 14#u32 bits x y j).toNat =
      proj_uN_0 ((Spec.Simd.swizzleWords x.bv)[Spec.Simd.byteAt y.bv j]!) := by
  change (selectedByte false x.bv y.bv (laneBits 8 j y.bv).toNat).toNat = _
  rw [laneBits_toNat]
  change (selectedByte false x.bv y.bv (Spec.Simd.byteAt y.bv j)).toNat = _
  rw [Spec.Simd.swizzleWords_get _ _ (Spec.Simd.byteAt_bound _ _)]
  by_cases first : Spec.Simd.byteAt y.bv j < 16
  · simp only [selectedByte,if_pos first]
    exact laneBits_toNat 8 _ x.bv
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
    rw [←laneBits_toNat,lanes j valid,swizzle_byte_source]
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

end Exec.Interp.Simd
