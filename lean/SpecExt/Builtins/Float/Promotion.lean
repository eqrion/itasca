import SpecExt.Builtins.Float.RoundExact
import SpecExt.Builtins.Float.Convert
import SpecExt.Builtins.Float.Lemmas
namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem promotion_normal_value (fraction : Nat) (exponent : Int) :
    magnitudeValue 64 (.NORM (fraction * 2^29) exponent) =
      magnitudeValue 32 (.NORM fraction exponent) := by
  simp only [magnitudeValue, fun_M, signif]
  change ((2^52 + fraction * 2^29 : Nat) : Rat) * powTwo (exponent - 52) = ((2^23 + fraction : Nat) : Rat) * powTwo (exponent - 23)
  have exponentEq : exponent - 23 = 29 + (exponent - 52) := by omega
  rw [exponentEq, powTwo_add]
  rw [show powTwo 29 = 536870912 by decide +kernel]
  push_cast
  ring

theorem promotion_subnormal_value (fraction shifts : Nat)
    (normalized : 8388608 ≤ fraction * 2^shifts) :
    magnitudeValue 64 (.NORM ((fraction * 2^shifts - 8388608) * 2^29) (-126 - (shifts : Int))) =
      magnitudeValue 32 (.SUBNORM fraction) := by
  simp only [magnitudeValue, fun_M, signif, floatBias, E, expon]
  change ((2^52 + (fraction * 2^shifts - 8388608) * 2^29 : Nat) : Rat) * powTwo (-126 - (shifts : Int) - 52) = (fraction : Rat) * powTwo (-149)
  have significand : 2^52 + (fraction * 2^shifts - 8388608) * 2^29 = fraction * 2^shifts * 2^29 := by omega
  rw [significand]
  have exponentEq : -126 - (shifts : Int) - 52 = -149 - ((shifts : Int) + 29) := by omega
  rw [exponentEq]
  have combine : powTwo ((shifts : Int) + 29) * powTwo (-149 - ((shifts : Int) + 29)) = powTwo (-149) := by
    rw [← powTwo_add]
    rw [show ((shifts : Int) + 29) + (-149 - ((shifts : Int) + 29)) = -149 by omega]
  have scale : ((2^shifts * 2^29 : Nat) : Rat) = powTwo ((shifts : Int) + 29) := by
    rw [powTwo_add]
    rw [show powTwo 29 = 536870912 by decide +kernel]
    simp [powTwo, show ¬(shifts : Int) < 0 by omega]
  rw [Nat.mul_assoc, Nat.cast_mul, scale, mul_assoc, combine]



set_option maxRecDepth 2048

theorem promotion_normal_mem (sign : Bool) (exponent fraction : Nat)
    (normal : 0 < exponent ∧ exponent < 255) (small : fraction < 8388608) :
    floatOfBits 64 ((if sign then 9223372036854775808 else 0) +
      ((exponent + 896) * 4503599627370496 + fraction * 536870912)) ∈
    promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + (exponent * 8388608 + fraction))) := by
  have targetSmall : fraction * 536870912 < 4503599627370496 := by omega
  have targetExponent : exponent + 896 < 2048 := by omega
  let bits := (exponent + 896) * 4503599627370496 + fraction * 536870912
  have expEq : ((exponent + 896 : Nat) : Int) - 1023 = (exponent : Int) - 127 := by omega
  have decoded : floatOfBits 64 bits = .POS (.NORM (fraction * 536870912) ((exponent : Int) - 127)) := by
    dsimp [bits]
    rw [decodeFieldsPos64 _ _ (by omega) (by omega)]
    simp only [show exponent + 896 ≠ 0 by omega, show exponent + 896 ≠ 2047 by omega, ↓reduceIte, expEq]
  have value : finiteValue 64 (floatOfBits 64 bits) = magnitudeValue 32 (.NORM fraction ((exponent : Int) - 127)) := by
    rw [decoded]
    exact promotion_normal_value fraction ((exponent : Int) - 127)
  have pos : 0 < bits := by dsimp [bits]; clear targetSmall targetExponent; omega
  have finite : bits + 1 < 9218868437227405312 := by dsimp [bits]; clear targetSmall targetExponent; omega
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    rw [decodeFieldsPos32 _ _ (by omega) small]
    simp only [show exponent ≠ 0 by omega, show exponent ≠ 255 by omega, ↓reduceIte]
    simp [promote__, demote__, isNaN, isInf, isZero, magnitude, negative, finiteValue,
      Bool.false_eq_true, Bool.or_false, ↓reduceIte, List.mem_singleton]
    exact (round_exact_positive64 bits pos finite).symm.trans (by rw [value])
  · simp only [↓reduceIte]
    rw [decodeFieldsNeg32 _ _ (by omega) small]
    rw [decodeFieldsNeg64 (exponent + 896) (fraction * 536870912) targetExponent targetSmall]
    simp only [show exponent ≠ 0 by omega, show exponent ≠ 255 by omega,
      show exponent + 896 ≠ 0 by omega, show exponent + 896 ≠ 2047 by omega, ↓reduceIte, expEq]
    simp [promote__, demote__, isNaN, isInf, isZero, magnitude, negative, finiteValue,
      Bool.false_eq_true, Bool.or_false, ↓reduceIte, List.mem_singleton]
    have exactRound := round_exact_negative64 bits pos finite
    rw [value, decoded] at exactRound
    exact exactRound.symm

theorem packed_or (high low width : Nat) (small : low < 2^width) :
    (high * 2^width ||| low) = high * 2^width + low := by
  have div : (high * 2^width ||| low) / 2^width = high := by
    rw [Nat.or_div_two_pow]
    simp [Nat.div_eq_of_lt small]
  have mod : (high * 2^width ||| low) % 2^width = low := by
    rw [Nat.or_mod_two_pow]
    simp [Nat.mod_eq_of_lt small]
  have decomposition := Nat.mod_add_div (high * 2^width ||| low) (2^width)
  rw [div, mod] at decomposition
  simpa [Nat.mul_comm, Nat.add_comm] using decomposition.symm

theorem promotion_subnormal_mem (sign : Bool) (fraction shifts : Nat)
    (positive : 0 < fraction) (small : fraction < 8388608) (count : shifts ≤ 24)
    (normalized : 8388608 ≤ fraction * 2^shifts ∧ fraction * 2^shifts < 16777216) :
    floatOfBits 64 ((if sign then 9223372036854775808 else 0) +
      ((897 - shifts) * 4503599627370496 + (fraction * 2^shifts - 8388608) * 536870912)) ∈
    promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + fraction)) := by
  have targetSmall : (fraction * 2^shifts - 8388608) * 536870912 < 4503599627370496 := by omega
  have targetExponent : 897-shifts < 2048 := by omega
  let bits := (897 - shifts) * 4503599627370496 + (fraction * 2^shifts - 8388608) * 536870912
  have expEq : ((897 - shifts : Nat) : Int) - 1023 = -126 - (shifts : Int) := by omega
  have decoded : floatOfBits 64 bits = .POS (.NORM ((fraction * 2^shifts - 8388608) * 536870912) (-126 - (shifts : Int))) := by
    dsimp [bits]
    rw [decodeFieldsPos64 _ _ (by omega) (by omega)]
    simp only [show 897-shifts ≠ 0 by omega, show 897-shifts ≠ 2047 by omega, ↓reduceIte, expEq]
  have value : finiteValue 64 (floatOfBits 64 bits) = magnitudeValue 32 (.SUBNORM fraction) := by
    rw [decoded]
    exact promotion_subnormal_value fraction shifts normalized.1
  have pos : 0 < bits := by dsimp [bits]; clear targetSmall targetExponent; omega
  have finite : bits + 1 < 9218868437227405312 := by dsimp [bits]; clear targetSmall targetExponent; omega
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    have source : floatOfBits 32 fraction = .POS (.SUBNORM fraction) := by
      simpa using decodeFieldsPos32 0 fraction (by omega) small
    rw [source]
    simp [promote__, demote__, isNaN, isInf, isZero, magnitude, negative, finiteValue,
      beq_eq_decide, show fraction ≠ 0 by omega]
    exact (round_exact_positive64 bits pos finite).symm.trans (by rw [value])
  · simp only [↓reduceIte]
    have source : floatOfBits 32 (2147483648 + fraction) = .NEG (.SUBNORM fraction) := by
      simpa using decodeFieldsNeg32 0 fraction (by omega) small
    rw [source, decodeFieldsNeg64 (897 - shifts) ((fraction * 2^shifts - 8388608) * 536870912) targetExponent targetSmall]
    simp only [show 897-shifts ≠ 0 by omega, show 897-shifts ≠ 2047 by omega, ↓reduceIte, expEq]
    simp [promote__, demote__, isNaN, isInf, isZero, magnitude, negative, finiteValue,
      beq_eq_decide, show fraction ≠ 0 by omega]
    have exactRound := round_exact_negative64 bits pos finite
    rw [value, decoded] at exactRound
    exact exactRound.symm

theorem promotion_zero_mem (sign : Bool) :
    floatOfBits 64 (if sign then 9223372036854775808 else 0) ∈
      promote__ 32 64 (floatOfBits 32 (if sign then 2147483648 else 0)) := by
  cases sign <;> decide +kernel

theorem promotion_infinity_mem (sign : Bool) :
    floatOfBits 64 ((if sign then 9223372036854775808 else 0) + 9218868437227405312) ∈
      promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + 2139095040)) := by
  cases sign <;> decide +kernel

theorem promotion_nan_mem (sign : Bool) (fraction : Nat) (positive : 0 < fraction) (small : fraction < 8388608) :
    floatOfBits 64 9221120237041090560 ∈
      promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + (255 * 8388608 + fraction))) := by
  have canonical : floatOfBits 64 9221120237041090560 = fN.POS (.NAN (canon_ 64)) := by decide +kernel
  rw [canonical]
  cases sign
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    rw [decodeFieldsPos32 255 fraction (by decide) small]
    simp only [show 255 ≠ 0 by decide, show fraction ≠ 0 by omega, ↓reduceIte]
    simp only [promote__, demote__, isNaN, magnitude, ↓reduceIte]
    split
    · exact positive_canonical_mem 64
    · exact positive_canonical_mem_arithmetic 64 (by decide)
  · simp only [↓reduceIte]
    rw [decodeFieldsNeg32 255 fraction (by decide) small]
    simp only [show 255 ≠ 0 by decide, show fraction ≠ 0 by omega, ↓reduceIte]
    simp only [promote__, demote__, isNaN, magnitude, ↓reduceIte]
    split
    · exact positive_canonical_mem 64
    · exact positive_canonical_mem_arithmetic 64 (by decide)

end SpecExt.Builtins.Float

namespace SpecExt.Builtins.Float

theorem packed_float64 (sign : Bool) (exponent fraction : Nat)
    (exponentBound : exponent < 2048) (fractionBound : fraction < 4503599627370496) :
    ((if sign then 9223372036854775808 else 0) ||| exponent * 4503599627370496 ||| fraction) =
      (if sign then 9223372036854775808 else 0) + (exponent * 4503599627370496 + fraction) := by
  rw [Nat.or_assoc]
  have packed := packed_or exponent fraction 52 fractionBound
  norm_num only [Nat.reducePow] at packed
  rw [packed]
  cases sign
  · simp
  · change (1 * 2^63 ||| (exponent * 4503599627370496 + fraction)) = 1 * 2^63 + _
    apply packed_or
    omega

end SpecExt.Builtins.Float
