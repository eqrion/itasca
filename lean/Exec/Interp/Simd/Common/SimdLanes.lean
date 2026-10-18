import Exec.Interp.Numeric.Integer.Int
import SpecExt.Builtins.Lanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem mask (width : U32) (bound : width.val < 128) :
    runtime.interp.simd.mask width ⦃ result => result.val = 2^width.val - 1 ⦄ := by
  unfold runtime.interp.simd.mask
  step as ⟨power, powerEq, powerBits⟩
  have powerValue : power.val = 2^width.val := by
    rw [powerEq]
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    simp only [U128.size, U128.numBits, UScalarTy.U128_numBits_eq]
    exact Nat.pow_lt_pow_right (by decide) bound
  have positive : 1 ≤ power.val := by rw [powerValue]; exact Nat.one_le_pow _ _ (by decide)
  step
  scalar_tac

@[step] theorem lane (v : U128) (width index : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (positionBound : width.val * index.val < 128) :
    runtime.interp.simd.lane v width index ⦃ result =>
      result.val = v.val / 2^(width.val * index.val) % 2^width.val ⦄ := by
  unfold runtime.interp.simd.lane
  step as ⟨position, positionEq⟩
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  step with mask width (by omega) as ⟨maskValue, maskEq⟩
  simp only [lift, bind_ok, WP.spec_ok]
  rw [UScalar.cast_val_eq, UScalar.val_and, maskEq, Nat.and_two_pow_sub_one_eq_mod,
    shiftedEq, Nat.shiftRight_eq_div_pow, positionEq]
  apply Nat.mod_eq_of_lt
  exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    (Nat.pow_le_pow_right (by decide) widthBound)

@[step] theorem put (v : U128) (width index : U32) (x : U64)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (positionBound : width.val * index.val < 128) :
    runtime.interp.simd.put v width index x ⦃ result =>
      result.bv =
        (v.bv &&& ~~~((BitVec.ofNat 128 (2^width.val-1)) <<< (width.val*index.val))) |||
        (((x.bv.setWidth 128) &&& (BitVec.ofNat 128 (2^width.val-1))) <<< (width.val*index.val)) ⦄ := by
  unfold runtime.interp.simd.put
  step as ⟨position, positionEq⟩
  step with mask width (by omega) as ⟨maskValue, maskEq⟩
  have maskBits : maskValue.bv = BitVec.ofNat 128 (2^width.val-1) := by
    rw [←maskEq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    change maskValue.val = maskValue.val % 2^128
    exact (Nat.mod_eq_of_lt (by scalar_tac)).symm
  step as ⟨shiftedMask, shiftedMaskEq, shiftedMaskBits⟩
  simp only [lift,bind_ok]
  step as ⟨shiftedValue, shiftedValueEq, shiftedValueBits⟩
  simp only [WP.spec_ok,UScalar.bv_or,UScalar.bv_and,UScalar.bv_not,
    shiftedMaskBits,shiftedValueBits,maskBits,positionEq]
  rfl
end Exec.Interp.Simd
