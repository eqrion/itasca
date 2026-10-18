import Exec.Interp.Numeric.Float.FloatTruncTail
import Exec.Interp.Numeric.Float.FloatCompareBits
import SpecExt.Builtins.Float.TruncBounds
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

@[step] theorem trunc_int64_sound (bits : U64) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    runtime.interp.float.trunc_int bits false width signed saturating ⦃ result =>
      TruncOutcome (if saturating then trunc_sat__ 64 width.val (if signed then .S else .U) (floatOfBits 64 bits.val)
        else trunc__ 64 width.val (if signed then .S else .U) (floatOfBits 64 bits.val)) result ⦄ := by
  let negative := decide (9223372036854775808 ≤ bits.val)
  let exponent := bits.val / 4503599627370496 % 2048
  let fraction := bits.val % 4503599627370496
  have bitsBound : bits.val < 2^64 := by scalar_tac
  have exponentBound : exponent < 2048 := Nat.mod_lt _ (by decide)
  have fractionBound : fraction < 4503599627370496 := Nat.mod_lt _ (by decide)
  have widthNat : width.val = 32 ∨ width.val = 64 := by rcases validWidth with rfl | rfl <;> simp
  have negativeEq : ((bits &&& 9223372036854775808#u64) != 0#u64) = negative := by
    rw [float_sign_mask_64 bits bitsBound]
    dsimp [negative]
    split <;> simp_all
  unfold runtime.interp.float.trunc_int
  simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok, negativeEq]
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  have exponentMask : ((UScalar.cast .U32 shifted) &&& 2047#u32).val = exponent := by
    rw [UScalar.val_and]
    change ((UScalar.cast .U32 shifted).val &&& (2^11-1)) = exponent
    rw [Nat.and_two_pow_sub_one_eq_mod, UScalar.cast_val_eq, shiftedEq, Nat.shiftRight_eq_div_pow]
    dsimp [exponent]
    norm_num only [UScalarTy.numBits, Nat.reducePow]
    omega
  step as ⟨radix, radixEq, radixBits⟩
  have radixValue : radix.val = 4503599627370496 := by
    rw [radixEq]
    norm_num [Nat.shiftLeft_eq, U64.size, U64.numBits]
  step as ⟨mask, maskEq⟩
  have fractionMask : (bits &&& mask).val = fraction := by
    rw [UScalar.val_and, maskEq, radixValue]
    exact Nat.and_two_pow_sub_one_eq_mod bits.val 52
  split
  · have maxExponent : exponent = 2047 := by scalar_tac
    split
    · have positiveFraction : 0 < fraction := by scalar_tac
      have nan : isNaN (floatOfBits 64 bits.val) = true := by
        rw [isNaN_floatOfBits_64]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent positiveFraction
        omega
      rw [nan_conversion 64 width.val signed saturating _ nan]
      cases saturating <;> simp [TruncOutcome]
    · have zeroFraction : fraction = 0 := by scalar_tac
      have nan : isNaN (floatOfBits 64 bits.val) = false := by
        rw [isNaN_floatOfBits_64]
        simp only [decide_eq_false_iff_not]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      have infinity : isInf (floatOfBits 64 bits.val) = true := by
        rw [isInf_floatOfBits_64]
        simp only [decide_eq_true_eq]
        dsimp [exponent, fraction] at maxExponent zeroFraction
        omega
      rw [infinity_conversion 64 width.val signed saturating _ widthNat nan infinity,
        negative_floatOfBits_64 bits.val bitsBound]
      apply WP.spec_mono (overflow_effect negative width signed saturating validWidth)
      intro result effect
      cases saturating
      · simp only [Bool.false_eq_true, ↓reduceIte] at effect ⊢
        rw [effect]
        exact ⟨rfl, Or.inl rfl⟩
      · simp only [↓reduceIte] at effect ⊢
        rcases effect with ⟨value, rfl, equality⟩
        simp [TruncOutcome, equality, negative]
  · have finiteExponent : exponent < 2047 := by scalar_tac
    have finite : bits.val % 9223372036854775808 < 9218868437227405312 := by
      dsimp [exponent] at finiteExponent
      omega
    rw [finite_conversion64 width.val bits.val signed saturating bitsBound finite]
    split
    · have tiny : exponent < 1023 := by scalar_tac
      have magnitudeZero : rawTruncMagnitude 52 1023 exponent fraction = 0 := by simp [rawTruncMagnitude, tiny]
      simp only [WP.spec_ok]
      change TruncOutcome (convertMagnitude width.val negative signed saturating (rawTruncMagnitude 52 1023 exponent fraction)) (.Ok 0#u64)
      rw [magnitudeZero, convertMagnitude_zero _ _ _ _ widthNat]
      rfl
    · have normal : 1023 ≤ exponent := by scalar_tac
      step as ⟨power, powerEq⟩
      have powerValue : power.val = exponent-1023 := by rw [powerEq, exponentMask]
      split
      · have large : 64 ≤ exponent-1023 := by scalar_tac
        exact overflow_convertMagnitude negative width signed saturating validWidth _
          (rawTruncMagnitude_large 52 1023 exponent fraction width.val negative signed widthNat large fractionBound)
      · have small : exponent-1023 < 64 := by scalar_tac
        have magnitudeBound := rawTruncMagnitude_u64 52 1023 exponent fraction small fractionBound
        have significand : (bits &&& mask ||| radix).val = 4503599627370496+fraction := by
          rw [UScalar.val_or, fractionMask, radixValue]
          rw [Nat.or_comm]
          simpa using (Nat.two_pow_add_eq_or_of_lt (show fraction < 2^52 from fractionBound) 1).symm
        split
        · have leftShift : 52 ≤ exponent-1023 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 52 1023 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftLeft_eq]
            have raw : rawTruncMagnitude 52 1023 exponent fraction =
                (4503599627370496+fraction)*2^(exponent-1023-52) := by
              simp [rawTruncMagnitude, show ¬exponent < 1023 from by omega, leftShift]
            rw [← raw]
            exact Nat.mod_eq_of_lt (by simpa [U64.size, U64.numBits] using magnitudeBound)
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
        · have rightShift : exponent-1023 < 52 := by scalar_tac
          step as ⟨shift, shiftEq⟩
          step as ⟨magnitude, magnitudeEq, magnitudeBits⟩
          have magnitudeValue : magnitude.val = rawTruncMagnitude 52 1023 exponent fraction := by
            rw [magnitudeEq, significand, shiftEq, powerValue, Nat.shiftRight_eq_div_pow]
            simp [rawTruncMagnitude, show ¬exponent < 1023 from by omega, show ¬52 ≤ exponent-1023 from by omega]
          have effect := checked_magnitude_effect magnitude negative width signed saturating validWidth
          simp only [checkedTruncMagnitude, lift, bind_ok] at effect
          rw [magnitudeValue] at effect
          exact effect
end Exec.Interp
