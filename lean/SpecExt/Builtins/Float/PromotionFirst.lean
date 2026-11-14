import SpecExt.Builtins.Float.MinMax
import SpecExt.Builtins.Float.Sign
import «wasm2.0»
import Mathlib.Tactic
import Mathlib.Data.Rat.Floor

/-!
Sections, each formerly its own module: RoundExact, Promotion, TruncRange, Truncation, TruncSemantics, TruncBounds, Examples, FirstChoice, MinMaxFirst, PromotionFirst.
-/

/-! ## RoundExact -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem floorEncoding_exact (width : Nat) (square : Bool) (q : Rat)
    (fuel lo hi target : Nat) (lower : lo ≤ target) (upper : target ≤ hi)
    (size : hi - lo < 2 ^ fuel)
    (test : ∀ k, lo ≤ k → k ≤ hi →
      ((if square then roundingValue width k * roundingValue width k else roundingValue width k) ≤ q ↔ k ≤ target)) :
    floorEncoding width square q fuel lo hi = target := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [floorEncoding]
    simp only [pow_zero] at size
    omega
  | succ fuel ih =>
    have power : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by omega
    rw [power] at size
    have lowMid : lo ≤ (lo + hi + 1) / 2 := by omega
    have midHigh : (lo + hi + 1) / 2 ≤ hi := by omega
    simp only [floorEncoding, test _ lowMid midHigh]
    split_ifs with mid
    · apply ih _ hi mid upper (by omega)
      intro k hk kh
      exact test k (by omega) kh
    · apply ih lo _ lower (by omega) (by omega)
      intro k hk kh
      exact test k hk (by omega)

theorem roundingValue_finite32 (bits : Nat) (finite : bits < 2139095040) :
    roundingValue 32 bits = finiteValue 32 (floatOfBits 32 bits) := by
  unfold roundingValue
  rw [if_neg (show bits ≠ infinityBits 32 by change bits ≠ 2139095040; omega)]
  unfold finiteValue
  rw [negative_floatOfBits_32 bits (by omega)]
  simp [show ¬2147483648 ≤ bits by omega]

theorem roundMagnitude_exact32 (bits : Nat) (finite : bits + 1 < 2139095040) :
    roundMagnitude 32 false (finiteValue 32 (floatOfBits 32 bits)) = magnitude (floatOfBits 32 bits) := by
  have floor : floorEncoding 32 false (finiteValue 32 (floatOfBits 32 bits)) 32 0
      (infinityBits 32 - 1) = bits := by
    apply floorEncoding_exact
    · omega
    · change bits ≤ 2139095040 - 1; omega
    · decide
    · intro k lower upper
      have kfinite : k < 2139095040 := by change k ≤ 2139095040 - 1 at upper; omega
      simp only [Bool.false_eq_true, ↓reduceIte, roundingValue_finite32 k kfinite]
      have lt := positive_finite_lt_32 bits k (by omega) kfinite
      simpa only [not_lt] using not_congr lt
  unfold roundMagnitude
  rw [floor]
  dsimp only
  rw [roundingValue_finite32 bits (by omega), roundingValue_finite32 (bits+1) finite]
  have rise := (positive_finite_lt_32 bits (bits+1) (by omega) finite).mpr (by omega)
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by linarith)]

theorem round_exact_positive32 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 2139095040) :
    round 32 (finiteValue 32 (floatOfBits 32 bits)) = floatOfBits 32 bits := by
  have zero : finiteValue 32 (floatOfBits 32 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 32 (floatOfBits 32 bits) := by
    have h := (positive_finite_lt_32 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_gt pos), if_neg (not_lt.mpr (le_of_lt pos)), roundMagnitude_exact32 bits finite]
  rw [← floatOfBits_abs32, Nat.mod_eq_of_lt (show bits < 2147483648 by omega)]

theorem roundingValue_finite64 (bits : Nat) (finite : bits < 9218868437227405312) :
    roundingValue 64 bits = finiteValue 64 (floatOfBits 64 bits) := by
  unfold roundingValue
  rw [if_neg (show bits ≠ infinityBits 64 by change bits ≠ 9218868437227405312; omega)]
  unfold finiteValue
  rw [negative_floatOfBits_64 bits (by omega)]
  simp [show ¬9223372036854775808 ≤ bits by omega]

theorem roundMagnitude_exact64 (bits : Nat) (finite : bits + 1 < 9218868437227405312) :
    roundMagnitude 64 false (finiteValue 64 (floatOfBits 64 bits)) = magnitude (floatOfBits 64 bits) := by
  have floor : floorEncoding 64 false (finiteValue 64 (floatOfBits 64 bits)) 64 0
      (infinityBits 64 - 1) = bits := by
    apply floorEncoding_exact
    · omega
    · change bits ≤ 9218868437227405312 - 1; omega
    · decide
    · intro k lower upper
      have kfinite : k < 9218868437227405312 := by change k ≤ 9218868437227405312 - 1 at upper; omega
      simp only [Bool.false_eq_true, ↓reduceIte, roundingValue_finite64 k kfinite]
      have lt := positive_finite_lt_64 bits k (by omega) kfinite
      simpa only [not_lt] using not_congr lt
  unfold roundMagnitude
  rw [floor]
  dsimp only
  rw [roundingValue_finite64 bits (by omega), roundingValue_finite64 (bits+1) finite]
  have rise := (positive_finite_lt_64 bits (bits+1) (by omega) finite).mpr (by omega)
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by linarith)]

theorem round_exact_positive64 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 9218868437227405312) :
    round 64 (finiteValue 64 (floatOfBits 64 bits)) = floatOfBits 64 bits := by
  have zero : finiteValue 64 (floatOfBits 64 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 64 (floatOfBits 64 bits) := by
    have h := (positive_finite_lt_64 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_gt pos), if_neg (not_lt.mpr (le_of_lt pos)), roundMagnitude_exact64 bits finite]
  rw [← floatOfBits_abs64, Nat.mod_eq_of_lt (show bits < 9223372036854775808 by omega)]

theorem round_exact_negative32 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 2139095040) :
    round 32 (-finiteValue 32 (floatOfBits 32 bits)) = .NEG (magnitude (floatOfBits 32 bits)) := by
  have zero : finiteValue 32 (floatOfBits 32 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 32 (floatOfBits 32 bits) := by
    have h := (positive_finite_lt_32 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_lt (neg_lt_zero.mpr pos)), if_pos (neg_lt_zero.mpr pos), neg_neg,
    roundMagnitude_exact32 bits finite]

theorem round_exact_negative64 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 9218868437227405312) :
    round 64 (-finiteValue 64 (floatOfBits 64 bits)) = .NEG (magnitude (floatOfBits 64 bits)) := by
  have zero : finiteValue 64 (floatOfBits 64 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 64 (floatOfBits 64 bits) := by
    have h := (positive_finite_lt_64 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_lt (neg_lt_zero.mpr pos)), if_pos (neg_lt_zero.mpr pos), neg_neg,
    roundMagnitude_exact64 bits finite]

end SpecExt.Builtins.Float

end

/-! ## Promotion -/

section

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

end

/-! ## TruncRange -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

def magnitudeLimit (width : Nat) (negative signed : Bool) : Nat :=
  if signed then if negative then 2^(width-1) else 2^(width-1)-1 else 2^width-1

def magnitudeBoundary (width : Nat) (negative signed : Bool) : Nat :=
  if signed then if negative then 2^(width-1) else 2^(width-1)-1
  else if negative then 0 else 2^width-1

def magnitudeWithin (width : Nat) (negative signed : Bool) (magnitude : Nat) : Prop :=
  magnitude ≤ magnitudeLimit width negative signed ∧ (negative = true → signed = false → magnitude = 0)

def convertMagnitude (width : Nat) (negative signed saturating : Bool) (magnitude : Nat) : Option iN :=
  let value : Int := if negative then -(magnitude : Int) else magnitude
  if saturating then some (saturate width (if signed then .S else .U) value)
  else
    let lower : Int := if signed then -(2:Int)^(width-1) else 0
    let upper : Int := if signed then (2:Int)^(width-1) else 2^width
    if lower ≤ value ∧ value < upper then some (encodeSigned width value) else none

theorem convertMagnitude_outside (width magnitude : Nat) (negative signed saturating : Bool)
    (validWidth : width = 32 ∨ width = 64) (outside : ¬magnitudeWithin width negative signed magnitude) :
    convertMagnitude width negative signed saturating magnitude =
      if saturating then some (.mk_uN (magnitudeBoundary width negative signed)) else none := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> cases saturating
  all_goals norm_num [convertMagnitude, magnitudeWithin, magnitudeLimit, magnitudeBoundary, saturate, encodeSigned,
    min_def, max_def] at *
  all_goals try split_ifs
  all_goals try simp_all
  all_goals omega

theorem convertMagnitude_inside (width magnitude : Nat) (negative signed saturating : Bool)
    (validWidth : width = 32 ∨ width = 64) (inside : magnitudeWithin width negative signed magnitude) :
    convertMagnitude width negative signed saturating magnitude =
      some (.mk_uN (if negative then (2^width-magnitude) % 2^width else magnitude)) := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> cases saturating
  all_goals norm_num [convertMagnitude, magnitudeWithin, magnitudeLimit, saturate, encodeSigned,
    min_def, max_def] at *
  all_goals try split_ifs
  all_goals try simp_all
  all_goals omega

end SpecExt.Builtins.Float

end

/-! ## Truncation -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem truncz_nonnegative (q : Rat) (nonnegative : 0 ≤ q) : truncz q = ⌊q⌋ := by
  rw [truncz, Int.tdiv_eq_ediv_of_nonneg (Rat.num_nonneg.mpr nonnegative), Rat.floor_def']
  rfl

theorem truncz_neg (q : Rat) : truncz (-q) = -truncz q := by
  simp [truncz, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.neg_tdiv]

theorem truncz_natural (n : Nat) : truncz (n : Rat) = n := by
  rw [truncz_nonnegative _ (by positivity)]
  simp

theorem truncz_natural_div (n d : Nat) : truncz ((n : Rat) / (d : Rat)) = (n / d : Nat) := by
  rw [truncz_nonnegative _ (by positivity), Rat.floor_natCast_div_natCast, Int.natCast_div]

theorem powTwo_neg_nat (n : Nat) : powTwo (-(n : Int)) = 1 / (2 : Rat)^n := by
  rw [powTwo_eq_zpow, zpow_neg, zpow_natCast, one_div]

theorem truncz_scaled_natural (n shift : Nat) :
    truncz ((n : Rat) * powTwo (-(shift : Int))) = (n / 2^shift : Nat) := by
  rw [powTwo_neg_nat, ← div_eq_mul_one_div]
  have castPower : ((2^shift : Nat) : Rat) = (2:Rat)^shift := by push_cast; rfl
  rw [← castPower, truncz_natural_div]

theorem mul_pow_div_pow (number exponent divisor : Nat) :
    number * 2^exponent / 2^divisor =
      if divisor ≤ exponent then number * 2^(exponent-divisor) else number / 2^(divisor-exponent) := by
  split_ifs with order
  · have decomposition : exponent = (exponent-divisor)+divisor := by omega
    conv_lhs => rw [decomposition, pow_add, ← Nat.mul_assoc]
    rw [Nat.mul_div_cancel _ (by positivity)]
  · have decomposition : divisor = exponent+(divisor-exponent) := by omega
    conv_lhs => rw [decomposition, pow_add, ← Nat.div_div_eq_div_mul]
    rw [Nat.mul_div_cancel _ (by positivity)]

theorem truncz_positive_finite32 (bits : Nat) (finite : bits < 2139095040) :
    truncz (finiteValue 32 (floatOfBits 32 bits)) =
      (positiveEncodingUnits 8388608 bits / 2^149 : Nat) := by
  rw [positive_finite_value_32 bits finite]
  exact truncz_scaled_natural _ 149

theorem truncz_positive_finite64 (bits : Nat) (finite : bits < 9218868437227405312) :
    truncz (finiteValue 64 (floatOfBits 64 bits)) =
      (positiveEncodingUnits 4503599627370496 bits / 2^1074 : Nat) := by
  rw [positive_finite_value_64 bits finite]
  exact truncz_scaled_natural _ 1074

def rawTruncMagnitude (fractionBits bias exponent fraction : Nat) : Nat :=
  if exponent < bias then 0 else
    if fractionBits ≤ exponent - bias then (2^fractionBits + fraction) * 2^(exponent-bias-fractionBits)
    else (2^fractionBits + fraction) / 2^(fractionBits-(exponent-bias))

theorem encodingUnits_trunc (fractionBits bias exponent fraction : Nat)
    (biasPositive : 0 < bias) (small : fraction < 2^fractionBits) :
    encodingUnits (2^fractionBits) exponent fraction / 2^(bias+fractionBits-1) =
      rawTruncMagnitude fractionBits bias exponent fraction := by
  unfold encodingUnits rawTruncMagnitude
  by_cases zero : exponent = 0
  · subst exponent
    simp only [if_true, biasPositive, ↓reduceIte]
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le small (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [if_neg zero, mul_pow_div_pow]
    by_cases tiny : exponent < bias
    · have order : ¬bias + fractionBits - 1 ≤ exponent - 1 := by omega
      simp only [order, tiny, ↓reduceIte]
      apply Nat.div_eq_of_lt
      have denominator : 2^(fractionBits+1) ≤ 2^(bias+fractionBits-1-(exponent-1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_succ] at denominator
      omega
    · simp only [tiny, ↓reduceIte]
      have order : (bias+fractionBits-1 ≤ exponent-1) ↔ fractionBits ≤ exponent-bias := by omega
      simp only [order]
      split
      · have same : exponent-1-(bias+fractionBits-1) = exponent-bias-fractionBits := by omega
        rw [same]
      · have same : bias+fractionBits-1-(exponent-1) = fractionBits-(exponent-bias) := by omega
        rw [same]

theorem truncz_floatOfBits32 (bits : Nat) (bound : bits < 2^32)
    (finite : bits % 2147483648 < 2139095040) :
    truncz (finiteValue 32 (floatOfBits 32 bits)) =
      if 2147483648 ≤ bits then -(rawTruncMagnitude 23 127 (bits / 8388608 % 256) (bits % 8388608) : Int)
      else (rawTruncMagnitude 23 127 (bits / 8388608 % 256) (bits % 8388608) : Int) := by
  have positiveValue : truncz (finiteValue 32 (floatOfBits 32 (bits % 2147483648))) =
      (rawTruncMagnitude 23 127 (bits / 8388608 % 256) (bits % 8388608) : Int) := by
    rw [truncz_positive_finite32 _ finite]
    congr 1
    unfold positiveEncodingUnits
    have exponent : bits % 2147483648 / 8388608 = bits / 8388608 % 256 := by omega
    have fraction : bits % 2147483648 % 8388608 = bits % 8388608 := by omega
    rw [exponent, fraction]
    exact encodingUnits_trunc 23 127 _ _ (by omega) (Nat.mod_lt _ (by decide))
  rw [finiteValue_signed_32 bits bound]
  split_ifs
  · rw [truncz_neg, positiveValue]
  · exact positiveValue

theorem truncz_floatOfBits64 (bits : Nat) (bound : bits < 2^64)
    (finite : bits % 9223372036854775808 < 9218868437227405312) :
    truncz (finiteValue 64 (floatOfBits 64 bits)) =
      if 9223372036854775808 ≤ bits then -(rawTruncMagnitude 52 1023 (bits / 4503599627370496 % 2048) (bits % 4503599627370496) : Int)
      else (rawTruncMagnitude 52 1023 (bits / 4503599627370496 % 2048) (bits % 4503599627370496) : Int) := by
  have positiveValue : truncz (finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808))) =
      (rawTruncMagnitude 52 1023 (bits / 4503599627370496 % 2048) (bits % 4503599627370496) : Int) := by
    rw [truncz_positive_finite64 _ finite]
    congr 1
    unfold positiveEncodingUnits
    have exponent : bits % 9223372036854775808 / 4503599627370496 = bits / 4503599627370496 % 2048 := by omega
    have fraction : bits % 9223372036854775808 % 4503599627370496 = bits % 4503599627370496 := by omega
    rw [exponent, fraction]
    exact encodingUnits_trunc 52 1023 _ _ (by omega) (Nat.mod_lt _ (by decide))
  rw [finiteValue_signed_64 bits bound]
  split_ifs
  · rw [truncz_neg, positiveValue]
  · exact positiveValue

theorem rawTruncMagnitude_normal_bound (fractionBits bias exponent fraction : Nat)
    (normal : bias ≤ exponent) (small : fraction < 2^fractionBits) :
    2^(exponent-bias) ≤ rawTruncMagnitude fractionBits bias exponent fraction ∧
      rawTruncMagnitude fractionBits bias exponent fraction < 2^(exponent-bias+1) := by
  unfold rawTruncMagnitude
  rw [if_neg (by omega)]
  split_ifs with larger
  · have power : 2^(exponent-bias) = 2^fractionBits * 2^(exponent-bias-fractionBits) := by
      rw [← pow_add]
      congr 1 <;> omega
    have next : 2^(exponent-bias+1) = 2^(exponent-bias)*2 := pow_succ _ _
    have positive : 0 < 2^(exponent-bias-fractionBits) := by positivity
    rw [power, next, power]
    constructor <;> nlinarith
  · have exponentPower : 2^fractionBits = 2^(exponent-bias) * 2^(fractionBits-(exponent-bias)) := by
      rw [← pow_add]
      congr 1 <;> omega
    have positive : 0 < 2^(fractionBits-(exponent-bias)) := by positivity
    constructor
    · apply (Nat.le_div_iff_mul_le positive).mpr
      rw [← exponentPower]
      omega
    · apply (Nat.div_lt_iff_lt_mul positive).mpr
      rw [pow_succ]
      have : (2^(exponent-bias)*2)*2^(fractionBits-(exponent-bias)) = 2^fractionBits*2 := by
        rw [exponentPower]
        ring
      rw [this]
      omega

end SpecExt.Builtins.Float

end

/-! ## TruncSemantics -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem finite_conversion32 (target bits : Nat) (signed saturating : Bool)
    (bound : bits < 2^32) (finite : bits % 2147483648 < 2139095040) :
    (if saturating then trunc_sat__ 32 target (if signed then .S else .U) (floatOfBits 32 bits)
      else trunc__ 32 target (if signed then .S else .U) (floatOfBits 32 bits)) =
    convertMagnitude target (decide (2147483648 ≤ bits)) signed saturating
      (rawTruncMagnitude 23 127 (bits / 8388608 % 256) (bits % 8388608)) := by
  have nan : isNaN (floatOfBits 32 bits) = false := by rw [isNaN_floatOfBits_32]; simp; omega
  have infinity : isInf (floatOfBits 32 bits) = false := by rw [isInf_floatOfBits_32]; simp; omega
  have value := truncz_floatOfBits32 bits bound finite
  cases signed <;> cases saturating <;>
    simp [trunc__, trunc_sat__, convertMagnitude, nan, infinity, value]

theorem finite_conversion64 (target bits : Nat) (signed saturating : Bool)
    (bound : bits < 2^64) (finite : bits % 9223372036854775808 < 9218868437227405312) :
    (if saturating then trunc_sat__ 64 target (if signed then .S else .U) (floatOfBits 64 bits)
      else trunc__ 64 target (if signed then .S else .U) (floatOfBits 64 bits)) =
    convertMagnitude target (decide (9223372036854775808 ≤ bits)) signed saturating
      (rawTruncMagnitude 52 1023 (bits / 4503599627370496 % 2048) (bits % 4503599627370496)) := by
  have nan : isNaN (floatOfBits 64 bits) = false := by rw [isNaN_floatOfBits_64]; simp; omega
  have infinity : isInf (floatOfBits 64 bits) = false := by rw [isInf_floatOfBits_64]; simp; omega
  have value := truncz_floatOfBits64 bits bound finite
  cases signed <;> cases saturating <;>
    simp [trunc__, trunc_sat__, convertMagnitude, nan, infinity, value]

theorem nan_conversion (source target : Nat) (signed saturating : Bool) (value : fN)
    (nan : isNaN value = true) :
    (if saturating then trunc_sat__ source target (if signed then .S else .U) value
      else trunc__ source target (if signed then .S else .U) value) =
      if saturating then some (.mk_uN 0) else none := by
  cases saturating <;> simp [trunc_sat__, trunc__, nan]

theorem infinity_conversion (source target : Nat) (signed saturating : Bool) (value : fN)
    (validWidth : target = 32 ∨ target = 64) (nan : isNaN value = false) (infinity : isInf value = true) :
    (if saturating then trunc_sat__ source target (if signed then .S else .U) value
      else trunc__ source target (if signed then .S else .U) value) =
      if saturating then some (.mk_uN (magnitudeBoundary target (negative value) signed)) else none := by
  cases saturating
  · simp [trunc__, nan, infinity]
  · simp only [↓reduceIte, trunc_sat__, nan, infinity, Bool.false_eq_true]
    have outside : ¬magnitudeWithin target (negative value) signed (2^target) := by
      rcases validWidth with rfl | rfl
      all_goals cases negative value <;> cases signed <;> norm_num [magnitudeWithin, magnitudeLimit]
    have converted := convertMagnitude_outside target (2^target) (negative value) signed true validWidth outside
    simpa [convertMagnitude] using converted

end SpecExt.Builtins.Float

end

/-! ## TruncBounds -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem convertMagnitude_zero (width : Nat) (negative signed saturating : Bool)
    (validWidth : width = 32 ∨ width = 64) :
    convertMagnitude width negative signed saturating 0 = some (.mk_uN 0) := by
  have inside : magnitudeWithin width negative signed 0 := by simp [magnitudeWithin]
  have effect := convertMagnitude_inside width 0 negative signed saturating validWidth inside
  cases negative <;> simpa using effect

theorem magnitudeLimit_bounded (width : Nat) (negative signed : Bool)
    (validWidth : width = 32 ∨ width = 64) : magnitudeLimit width negative signed < 2^64 := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> decide

theorem rawTruncMagnitude_large (fractionBits bias exponent fraction width : Nat)
    (negative signed : Bool) (validWidth : width = 32 ∨ width = 64)
    (power : 64 ≤ exponent-bias) (small : fraction < 2^fractionBits) :
    ¬magnitudeWithin width negative signed (rawTruncMagnitude fractionBits bias exponent fraction) := by
  have normal : bias ≤ exponent := by omega
  have bound := (rawTruncMagnitude_normal_bound fractionBits bias exponent fraction normal small).1
  have least : 2^64 ≤ 2^(exponent-bias) := Nat.pow_le_pow_right (by omega) power
  have limit := magnitudeLimit_bounded width negative signed validWidth
  intro inside
  have := inside.1
  omega

theorem rawTruncMagnitude_u64 (fractionBits bias exponent fraction : Nat)
    (power : exponent-bias < 64) (small : fraction < 2^fractionBits) :
    rawTruncMagnitude fractionBits bias exponent fraction < 2^64 := by
  by_cases tiny : exponent < bias
  · simp [rawTruncMagnitude, tiny]
  · have normal : bias ≤ exponent := by omega
    have bound := (rawTruncMagnitude_normal_bound fractionBits bias exponent fraction normal small).2
    have most : 2^(exponent-bias+1) ≤ 2^64 := Nat.pow_le_pow_right (by omega) (by omega)
    exact lt_of_lt_of_le bound most

end SpecExt.Builtins.Float

end

/-! ## Examples -/

section

/-! IEEE boundary vectors checked by kernel reduction, with no native evaluator.
The specification uses exact rationals and integer square comparisons. -/

namespace SpecExt.Builtins.Float.Examples
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def f32 (bits : Nat) : fN := floatOfBits 32 bits
private def f64 (bits : Nat) : fN := floatOfBits 64 bits

example : fadd_ 32 (f32 0x3f800000) (f32 0x40000000) = [f32 0x40400000] := by decide +kernel
example : fadd_ 32 (f32 0x3f800000) (f32 0x33800000) = [f32 0x3f800000] := by decide +kernel
example : fadd_ 32 (f32 0x3f800001) (f32 0x33800000) = [f32 0x3f800002] := by decide +kernel
example : fadd_ 32 (f32 0x80000000) (f32 0x80000000) = [f32 0x80000000] := by decide +kernel
example : fadd_ 32 (f32 0x80000000) (f32 0) = [f32 0] := by decide +kernel
example : fsub_ 32 (f32 0x3f800000) (f32 0x3f800000) = [f32 0] := by decide +kernel
example : fmul_ 32 (f32 0x7f7fffff) (f32 0x40000000) = [f32 0x7f800000] := by decide +kernel
example : fmul_ 32 (f32 1) (f32 0x3f000000) = [f32 0] := by decide +kernel
example : fmul_ 32 (f32 3) (f32 0x3f000000) = [f32 2] := by decide +kernel
example : fdiv_ 32 (f32 0xbf800000) (f32 0x7f800000) = [f32 0x80000000] := by decide +kernel
example : fsqrt_ 32 (f32 0x40800000) = [f32 0x40000000] := by decide +kernel
example : fsqrt_ 32 (f32 0x40000000) = [f32 0x3fb504f3] := by decide +kernel
example : fsqrt_ 32 (f32 0x80000000) = [f32 0x80000000] := by decide +kernel
example : fceil_ 32 (f32 0xbf000000) = [f32 0x80000000] := by decide +kernel
example : ffloor_ 32 (f32 0xbf000000) = [f32 0xbf800000] := by decide +kernel
example : fnearest_ 32 (f32 0x40200000) = [f32 0x40000000] := by decide +kernel
example : fnearest_ 32 (f32 0xc0600000) = [f32 0xc0800000] := by decide +kernel
example : feq_ 32 (f32 0x7fc00000) (f32 0x7fc00000) = .mk_uN 0 := by decide +kernel
example : feq_ 32 (f32 0) (f32 0x80000000) = .mk_uN 1 := by decide +kernel
example : flt_ 32 (f32 0xff800000) (f32 0xbf800000) = .mk_uN 1 := by decide +kernel
example : fmin_ 32 (f32 0) (f32 0x80000000) = [f32 0x80000000] := by decide +kernel
example : fmax_ 32 (f32 0) (f32 0x80000000) = [f32 0] := by decide +kernel
example : fpmin_ 32 (f32 0x7f800001) (f32 0x3f800000) = [f32 0x7f800001] := by decide +kernel
example : promote__ 32 64 (f32 1) = [f64 0x36a0000000000000] := by decide +kernel
example : demote__ 64 32 (f64 0x3ff0000010000000) = [f32 0x3f800000] := by decide +kernel
example : convert__ 32 32 .U (.mk_uN 16777217) = f32 0x4b800000 := by decide +kernel
example : trunc__ 32 32 .S (f32 0xcf000000) = some (.mk_uN 2147483648) := by decide +kernel
example : trunc__ 32 32 .S (f32 0x4f000000) = none := by decide +kernel
example : trunc_sat__ 32 32 .U (f32 0x7f800000) = some (.mk_uN 4294967295) := by decide +kernel
example : trunc_sat__ 32 32 .S (f32 0xff800000) = some (.mk_uN 2147483648) := by decide +kernel
example : trunc_sat__ 32 32 .S (f32 0x7fc00000) = some (.mk_uN 0) := by decide +kernel

end SpecExt.Builtins.Float.Examples

end

/-! ## FirstChoice -/

section

namespace SpecExt.Builtins.Float

/-- The pinned floating-point result sets are a singleton or one of the two
explicit NaN sets. Their ordering fixes a canonical first-result policy. -/
inductive ReplyFamily (width : Nat) : List fN → Prop where
  | singleton (value : fN) : ReplyFamily width [value]
  | canonical : ReplyFamily width (canonicalNaNs width)
  | arithmetic : ReplyFamily width (arithmeticNaNs width)

theorem nans_reply_family (width : Nat) (inputs : List fN) : ReplyFamily width (nans width inputs) := by
  unfold nans
  split <;> constructor

theorem arithmeticNaNs_head (width : Nat) (positive : 0<canon_ width) :
    (arithmeticNaNs width).head?=some (.POS (.NAN (canon_ width))) := by
  cases count : canon_ width with
  | zero => omega
  | succ n => simp [arithmeticNaNs,count,List.range_succ_eq_map]

theorem canonicalNaNs_member_isNaN {width : Nat} {value : fN} (member : value∈canonicalNaNs width) :
    isNaN value=true := by
  simp only [canonicalNaNs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem arithmeticNaNs_member_isNaN {width : Nat} {value : fN} (member : value∈arithmeticNaNs width) :
    isNaN value=true := by
  obtain ⟨offset,inside,member⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem ReplyFamily.head_of_canonical_result {width : Nat} {allowed : List fN} {value : fN}
    (family : ReplyFamily width allowed) (positive : 0<canon_ width) (member : value∈allowed)
    (canonical : isNaN value=true → value=.POS (.NAN (canon_ width))) : allowed.head?=some value := by
  cases family with
  | singleton result =>
    have same : value=result := List.mem_singleton.mp member
    rw [same]
    rfl
  | canonical =>
    have same := canonical (canonicalNaNs_member_isNaN member)
    rw [same]
    rfl
  | arithmetic =>
    have same := canonical (arithmeticNaNs_member_isNaN member)
    rw [same]
    exact arithmeticNaNs_head width positive


theorem add_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fadd_ width a b) := by
  unfold fadd_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem sub_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fsub_ width a b) := by
  unfold fsub_
  split
  · exact nans_reply_family _ _
  · exact add_reply_family _ _ _

theorem mul_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fmul_ width a b) := by
  unfold fmul_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem div_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fdiv_ width a b) := by
  unfold fdiv_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem sqrt_reply_family (width : Nat) (a : fN) : ReplyFamily width (fsqrt_ width a) := by
  unfold fsqrt_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem integral_reply_family (op : Rat → Int) (width : Nat) (a : fN) : ReplyFamily width (integral op width a) := by
  unfold integral
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem ceil_reply_family (width : Nat) (a : fN) : ReplyFamily width (fceil_ width a) := integral_reply_family _ _ _
theorem floor_reply_family (width : Nat) (a : fN) : ReplyFamily width (ffloor_ width a) := integral_reply_family _ _ _
theorem trunc_reply_family (width : Nat) (a : fN) : ReplyFamily width (ftrunc_ width a) := integral_reply_family _ _ _
theorem nearest_reply_family (width : Nat) (a : fN) : ReplyFamily width (fnearest_ width a) := integral_reply_family _ _ _

theorem min_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fmin_ width a b) := by
  unfold fmin_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem max_reply_family (width : Nat) (a b : fN) : ReplyFamily width (fmax_ width a b) := by
  unfold fmax_
  split_ifs <;> first | exact nans_reply_family _ _ | constructor

theorem demote_reply_family (source target : Nat) (a : fN) : ReplyFamily target (demote__ source target a) := by
  unfold demote__
  split_ifs <;> constructor

theorem promote_reply_family (source target : Nat) (a : fN) : ReplyFamily target (promote__ source target a) :=
  demote_reply_family _ _ _
end SpecExt.Builtins.Float

end

/-! ## MinMaxFirst -/

section

namespace SpecExt.Builtins.Float

theorem nans_head (width : Nat) (inputs : List fN) (positive : 0<canon_ width) :
    (nans width inputs).head?=some (.POS (.NAN (canon_ width))) := by
  unfold nans
  split
  · rfl
  · exact arithmeticNaNs_head width positive

theorem raw_min32_first_choice (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (fmin_ 32 (floatOfBits 32 a) (floatOfBits 32 b)).head?=some (floatOfBits 32 (if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then 2143289344
      else if rawEqual 2147483648 a b then a ||| b else if rawLess 2147483648 a b then a else b)) := by
  have member := raw_min32_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 32 a) || isNaN (floatOfBits 32 b))=true
  · apply (min_reply_family 32 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 := by
      simpa only [isNaN_floatOfBits_32,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 32 2143289344=fN.POS (.NAN (canon_ 32)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmin_ 32 (floatOfBits 32 a) (floatOfBits 32 b)=[value] := by
      unfold fmin_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

theorem raw_min64_first_choice (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (fmin_ 64 (floatOfBits 64 a) (floatOfBits 64 b)).head?=some (floatOfBits 64 (if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then 9221120237041090560
      else if rawEqual 9223372036854775808 a b then a ||| b else if rawLess 9223372036854775808 a b then a else b)) := by
  have member := raw_min64_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 64 a) || isNaN (floatOfBits 64 b))=true
  · apply (min_reply_family 64 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 := by
      simpa only [isNaN_floatOfBits_64,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 64 9221120237041090560=fN.POS (.NAN (canon_ 64)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmin_ 64 (floatOfBits 64 a) (floatOfBits 64 b)=[value] := by
      unfold fmin_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

theorem raw_max32_first_choice (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (fmax_ 32 (floatOfBits 32 a) (floatOfBits 32 b)).head?=some (floatOfBits 32 (if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then 2143289344
      else if rawEqual 2147483648 a b then a &&& b else if rawLess 2147483648 a b then b else a)) := by
  have member := raw_max32_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 32 a) || isNaN (floatOfBits 32 b))=true
  · apply (max_reply_family 32 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 := by
      simpa only [isNaN_floatOfBits_32,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 32 2143289344=fN.POS (.NAN (canon_ 32)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmax_ 32 (floatOfBits 32 a) (floatOfBits 32 b)=[value] := by
      unfold fmax_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

theorem raw_max64_first_choice (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (fmax_ 64 (floatOfBits 64 a) (floatOfBits 64 b)).head?=some (floatOfBits 64 (if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then 9221120237041090560
      else if rawEqual 9223372036854775808 a b then a &&& b else if rawLess 9223372036854775808 a b then b else a)) := by
  have member := raw_max64_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 64 a) || isNaN (floatOfBits 64 b))=true
  · apply (max_reply_family 64 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 := by
      simpa only [isNaN_floatOfBits_64,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 64 9221120237041090560=fN.POS (.NAN (canon_ 64)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmax_ 64 (floatOfBits 64 a) (floatOfBits 64 b)=[value] := by
      unfold fmax_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

end SpecExt.Builtins.Float

end

/-! ## PromotionFirst -/

section

namespace SpecExt.Builtins.Float

private theorem decoded64_not_nan_below_infinity (sign : Bool) (payload : Nat)
    (small : payload≤9218868437227405312) :
    isNaN (floatOfBits 64 ((if sign then 9223372036854775808 else 0)+payload))=false := by
  have remainder : payload % 9223372036854775808=payload := Nat.mod_eq_of_lt (by omega)
  cases sign <;> simp [isNaN_floatOfBits_64,Nat.add_mod,remainder,show ¬payload>9218868437227405312 by omega]

theorem promotion_normal_first_choice (sign : Bool) (exponent fraction : Nat)
    (normal : 0 < exponent ∧ exponent < 255) (small : fraction < 8388608) :
    (promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + (exponent * 8388608 + fraction)))).head?=some (floatOfBits 64 ((if sign then 9223372036854775808 else 0) +
      ((exponent + 896) * 4503599627370496 + fraction * 536870912))) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_normal_mem sign exponent fraction normal small)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign ((exponent+896)*4503599627370496+fraction*536870912) (by omega)
  rw [notNan] at nan
  contradiction

theorem promotion_subnormal_first_choice (sign : Bool) (fraction shifts : Nat)
    (positive : 0 < fraction) (small : fraction < 8388608) (count : shifts ≤ 24)
    (normalized : 8388608 ≤ fraction * 2^shifts ∧ fraction * 2^shifts < 16777216) :
    (promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + fraction))).head?=some (floatOfBits 64 ((if sign then 9223372036854775808 else 0) +
      ((897 - shifts) * 4503599627370496 + (fraction * 2^shifts - 8388608) * 536870912))) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_subnormal_mem sign fraction shifts positive small count normalized)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign ((897-shifts)*4503599627370496+(fraction*2^shifts-8388608)*536870912) (by omega)
  rw [notNan] at nan
  contradiction

theorem promotion_zero_first_choice (sign : Bool) :
    (  promote__ 32 64 (floatOfBits 32 (if sign then 2147483648 else 0))).head?=some (floatOfBits 64 (if sign then 9223372036854775808 else 0)) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_zero_mem sign)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign 0 (by omega)
  simp only [Nat.add_zero] at notNan
  rw [notNan] at nan
  contradiction

theorem promotion_infinity_first_choice (sign : Bool) :
    (  promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + 2139095040))).head?=some (floatOfBits 64 ((if sign then 9223372036854775808 else 0) + 9218868437227405312)) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_infinity_mem sign)
  intro nan
  have notNan := decoded64_not_nan_below_infinity sign 9218868437227405312 (by omega)
  rw [notNan] at nan
  contradiction

theorem promotion_nan_first_choice (sign : Bool) (fraction : Nat) (positive : 0 < fraction) (small : fraction < 8388608) :
    (  promote__ 32 64 (floatOfBits 32 ((if sign then 2147483648 else 0) + (255 * 8388608 + fraction)))).head?=some (floatOfBits 64 9221120237041090560) := by
  apply (promote_reply_family 32 64 _).head_of_canonical_result (by decide) (promotion_nan_mem sign fraction positive small)
  intro nan
  decide +kernel
end SpecExt.Builtins.Float

end
