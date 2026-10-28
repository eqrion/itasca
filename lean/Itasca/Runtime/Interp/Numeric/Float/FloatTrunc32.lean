import Itasca.Runtime.Interp.Numeric.Float.FloatTruncTail
import Itasca.Runtime.Interp.Numeric.Float.FloatCompareBits
import SpecExt.Builtins.Float.TruncBounds
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

theorem float_sign_mask32_unbounded (bits : U64) :
    bits &&& 2147483648#u64 = if 2147483648 ≤ (UScalar.cast .U32 bits).val then 2147483648#u64 else 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change bits.val &&& 2^31 = _
  rw [Nat.and_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.reducePow, UScalar.cast_val_eq, UScalarTy.numBits]
  have quotient : bits.val / 2147483648 % 2 = if 2147483648 ≤ bits.val % 4294967296 then 1 else 0 := by
    split <;> omega
  simp only [Nat.one_and_eq_mod_two, quotient]
  split <;> rfl

@[step] theorem trunc_int32_sound (bits : U64) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    runtime.interp.float.trunc_int bits true width signed saturating ⦃ result =>
      TruncOutcome (if saturating then trunc_sat__ 32 width.val (if signed then .S else .U) (floatOfBits 32 (UScalar.cast .U32 bits).val)
        else trunc__ 32 width.val (if signed then .S else .U) (floatOfBits 32 (UScalar.cast .U32 bits).val)) result ⦄ := by
  let negative := decide (2147483648 ≤ (UScalar.cast .U32 bits).val)
  let exponent := (UScalar.cast .U32 bits).val / 8388608 % 256
  let fraction := (UScalar.cast .U32 bits).val % 8388608
  have bitsBound : (UScalar.cast .U32 bits).val < 2^32 := by scalar_tac
  have castValue : (UScalar.cast .U32 bits).val = bits.val % 4294967296 := by simp [UScalar.cast_val_eq]
  have exponentBound : exponent < 256 := Nat.mod_lt _ (by decide)
  have fractionBound : fraction < 8388608 := Nat.mod_lt _ (by decide)
  have widthNat : width.val = 32 ∨ width.val = 64 := by rcases validWidth with rfl | rfl <;> simp
  have negativeEq : ((bits &&& 2147483648#u64) != 0#u64) = negative := by
    rw [float_sign_mask32_unbounded bits]
    dsimp [negative]
    split <;> simp_all
  unfold runtime.interp.float.trunc_int
  simp only [↓reduceIte, lift, bind_ok, negativeEq]
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  have exponentMask : ((UScalar.cast .U32 shifted) &&& 255#u32).val = exponent := by
    rw [UScalar.val_and]
    change ((UScalar.cast .U32 shifted).val &&& (2^8-1)) = exponent
    rw [Nat.and_two_pow_sub_one_eq_mod, UScalar.cast_val_eq, shiftedEq, Nat.shiftRight_eq_div_pow]
    dsimp [exponent]
    rw [castValue]
    norm_num only [UScalarTy.numBits, Nat.reducePow]
    omega
  step as ⟨radix, radixEq, radixBits⟩
  have radixValue : radix.val = 8388608 := by
    rw [radixEq]
    norm_num [Nat.shiftLeft_eq, U64.size, U64.numBits]
  step as ⟨mask, maskEq⟩
  have fractionMask : (bits &&& mask).val = fraction := by
    rw [UScalar.val_and, maskEq, radixValue]
    have packed := Nat.and_two_pow_sub_one_eq_mod bits.val 23
    dsimp [fraction]
    rw [castValue]
    norm_num only [Nat.reducePow] at packed
    omega
  split
  · have maxExponent : exponent = 255 := by scalar_tac
    split
    · have positiveFraction : 0 < fraction := by scalar_tac
      have nan : isNaN (floatOfBits 32 (UScalar.cast .U32 bits).val) = true := by
        rw [isNaN_floatOfBits_32]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent positiveFraction
        omega
      rw [nan_conversion 32 width.val signed saturating _ nan]
      cases saturating <;> simp [TruncOutcome]
    · have zeroFraction : fraction = 0 := by scalar_tac
      have nan : isNaN (floatOfBits 32 (UScalar.cast .U32 bits).val) = false := by
        rw [isNaN_floatOfBits_32]
        simp only [decide_eq_false_iff_not]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      have infinity : isInf (floatOfBits 32 (UScalar.cast .U32 bits).val) = true := by
        rw [isInf_floatOfBits_32]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      rw [infinity_conversion 32 width.val signed saturating _ widthNat nan infinity,
        negative_floatOfBits_32 (UScalar.cast .U32 bits).val bitsBound]
      apply WP.spec_mono (overflow_effect negative width signed saturating validWidth)
      intro result effect
      cases saturating
      · simp only [Bool.false_eq_true, ↓reduceIte] at effect ⊢
        rw [effect]
        exact ⟨rfl, Or.inl rfl⟩
      · simp only [↓reduceIte] at effect ⊢
        rcases effect with ⟨value, rfl, equality⟩
        simp [TruncOutcome, equality, negative]
  · have finiteExponent : exponent < 255 := by scalar_tac
    have finite : (UScalar.cast .U32 bits).val % 2147483648 < 2139095040 := by
      dsimp [exponent] at finiteExponent
      omega
    rw [finite_conversion32 width.val (UScalar.cast .U32 bits).val signed saturating bitsBound finite]
    split
    · have tiny : exponent < 127 := by scalar_tac
      have magnitudeZero : rawTruncMagnitude 23 127 exponent fraction = 0 := by simp [rawTruncMagnitude, tiny]
      simp only [WP.spec_ok]
      change TruncOutcome (convertMagnitude width.val negative signed saturating (rawTruncMagnitude 23 127 exponent fraction)) (.Ok 0#u64)
      rw [magnitudeZero, convertMagnitude_zero _ _ _ _ widthNat]
      rfl
    · have normal : 127 ≤ exponent := by scalar_tac
      step as ⟨power, powerEq⟩
      have powerValue : power.val = exponent-127 := by rw [powerEq, exponentMask]
      split
      · have large : 64 ≤ exponent-127 := by scalar_tac
        exact overflow_convertMagnitude negative width signed saturating validWidth _
          (rawTruncMagnitude_large 23 127 exponent fraction width.val negative signed widthNat large fractionBound)
      · have small : exponent-127 < 64 := by scalar_tac
        have magnitudeBound := rawTruncMagnitude_u64 23 127 exponent fraction small fractionBound
        have significand : (bits &&& mask ||| radix).val = 8388608+fraction := by
          rw [UScalar.val_or, fractionMask, radixValue]
          rw [Nat.or_comm]
          simpa using (Nat.two_pow_add_eq_or_of_lt (show fraction < 2^23 from fractionBound) 1).symm
        split
        · have leftShift : 23 ≤ exponent-127 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 23 127 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftLeft_eq]
            have raw : rawTruncMagnitude 23 127 exponent fraction =
                (8388608+fraction)*2^(exponent-127-23) := by
              simp [rawTruncMagnitude, show ¬exponent < 127 from by omega, leftShift]
            rw [← raw]
            exact Nat.mod_eq_of_lt (by simpa [U64.size, U64.numBits] using magnitudeBound)
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
        · have rightShift : exponent-127 < 23 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 23 127 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftRight_eq_div_pow]
            simp [rawTruncMagnitude, show ¬exponent < 127 from by omega, show ¬23 ≤ exponent-127 from by omega]
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
end Itasca.Runtime.Interp
