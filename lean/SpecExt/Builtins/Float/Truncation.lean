import SpecExt.Builtins.Float.Classify
import SpecExt.Builtins.Float.Convert
import Mathlib.Data.Rat.Floor
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
