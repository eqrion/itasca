import Exec.Interp.Simd.Common.SimdShuffleLoop
import Exec.Spec.SimdByteSelect
import SpecExt.Builtins.LaneMap
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shuffle_byte_source (bits x y : U128) (j : Nat)
    (bounded : Spec.Simd.byteAt bits.bv j < 32) :
    (shuffleByte 13#u32 bits x y j).toNat =
      proj_uN_0 ((Spec.Simd.byteWords x.bv ++ Spec.Simd.byteWords y.bv)[Spec.Simd.byteAt bits.bv j]!) := by
  change (selectedByte true x.bv y.bv (laneBits 8 j bits.bv).toNat).toNat = _
  rw [laneBits_toNat]
  change (selectedByte true x.bv y.bv (Spec.Simd.byteAt bits.bv j)).toNat = _
  rw [Spec.Simd.byteWords_append_get _ _ _ bounded]
  by_cases first : Spec.Simd.byteAt bits.bv j < 16
  · simp only [selectedByte,if_pos first]
    exact laneBits_toNat 8 _ x.bv
  · simp only [selectedByte,if_neg first,Bool.true_and,decide_eq_true_eq,if_pos bounded]
    exact laneBits_toNat 8 _ y.bv

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
    rw [←laneBits_toNat,lanes j valid,shuffle_byte_source bits x y j (bounded j valid)]
    dsimp only [values]
    rw [Spec.Simd.byteWords_get bits.bv j valid]
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
