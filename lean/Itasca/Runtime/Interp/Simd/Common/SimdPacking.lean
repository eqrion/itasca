import Itasca.Runtime.Interp.Simd.Common.SimdSplat
import SpecExt.Builtins.LaneView
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem laneBits_toNat (width index : Nat) (v : BitVec 128) :
    (laneBits width index v).toNat = v.toNat / 2^(width*index) % 2^width := by
  simp only [laneBits, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem packLanes_of_laneBits (ty : lanetype) (v : BitVec 128) (x : BitVec 64)
    (lanes : ∀ j, j < 128/lsize ty → laneBits (lsize ty) j v = x.setWidth (lsize ty)) :
    SpecExt.Builtins.packLanes ty
      (List.replicate (128/lsize ty) (SpecExt.Builtins.laneOfBits ty (x.setWidth (lsize ty)).toNat)) =
      v.toNat := by
  have eq := SpecExt.Builtins.pack_replicate_of_lanes ty (128/lsize ty) v.toNat
    (x.setWidth (lsize ty)).toNat (by
      intro j bound
      rw [←laneBits_toNat]
      exact congrArg BitVec.toNat (lanes j bound))
  have covers : lsize ty * (128/lsize ty) = 128 := by cases ty <;> decide
  rw [covers, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by rfl))] at eq
  exact eq

theorem splat_packed (ty : lanetype) (x : U64) (width : U32)
    (widthEq : width.val = lsize ty) :
    runtime.interp.simd.splat x width ⦃ result =>
      uN.mk_uN result.val = inv_lanes_ (.X ty (.mk_dim (128/lsize ty)))
        (List.replicate (128/lsize ty) (SpecExt.Builtins.laneOfBits ty (x.bv.setWidth (lsize ty)).toNat)) ⦄ := by
  apply WP.spec_mono (splat x width (by rw [widthEq]; cases ty <;> decide)
    (by rw [widthEq]; cases ty <;> decide))
  intro result lanes
  rw [widthEq] at lanes
  have eq := packLanes_of_laneBits ty result.bv x.bv lanes
  exact congrArg uN.mk_uN eq.symm

end Itasca.Runtime.Interp.Simd
