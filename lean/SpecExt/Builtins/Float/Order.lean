import SpecExt.Builtins.Float.Decoding
import Mathlib.Tactic
namespace SpecExt.Builtins.Float

/-- Positive finite IEEE encoding measured in units of the least subnormal. -/
def encodingUnits (radix exponent fraction : Nat) : Nat :=
  if exponent = 0 then fraction else (radix + fraction) * 2 ^ (exponent - 1)

theorem encodingUnits_same_exponent {radix exponent a b : Nat} (less : a < b) :
    encodingUnits radix exponent a < encodingUnits radix exponent b := by
  unfold encodingUnits
  split
  · exact less
  · exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

theorem encodingUnits_next_exponent {radix exponent a b : Nat}
    (bound : a < radix) :
    encodingUnits radix exponent a < encodingUnits radix (exponent + 1) b := by
  by_cases zero : exponent = 0
  · subst exponent
    simp [encodingUnits]
    omega
  · unfold encodingUnits
    simp only [zero, if_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      Nat.add_sub_cancel]
    have positive : 0 < 2 ^ (exponent - 1) := by positivity
    have power : 2 ^ exponent = 2 ^ (exponent - 1) * 2 := by
      conv_lhs => rw [show exponent = exponent - 1 + 1 by omega]
      rw [Nat.pow_succ]
    rw [power]
    nlinarith

theorem encodingUnits_exponent_monotone {radix a : Nat} (bound : a < radix) :
    StrictMono (fun exponent => encodingUnits radix exponent a) := by
  exact strictMono_nat_of_lt_succ (fun _ => encodingUnits_next_exponent bound)

theorem encodingUnits_lexicographic {radix exponent next a b : Nat}
    (bound : a < radix) (less : exponent < next) :
    encodingUnits radix exponent a < encodingUnits radix next b := by
  have first := encodingUnits_next_exponent (exponent := exponent) (b := 0) bound
  have later : encodingUnits radix (exponent + 1) 0 ≤ encodingUnits radix next 0 := by
    exact (encodingUnits_exponent_monotone (a := 0) (by omega)).monotone (by omega)
  have last : encodingUnits radix next 0 ≤ encodingUnits radix next b := by
    by_cases zero : b = 0
    · subst b; rfl
    · exact Nat.le_of_lt (encodingUnits_same_exponent (by omega))
  omega

def positiveEncodingUnits (radix bits : Nat) : Nat :=
  encodingUnits radix (bits / radix) (bits % radix)

theorem positiveEncodingUnits_strictMono (radix : Nat) (positive : 0 < radix) :
    StrictMono (positiveEncodingUnits radix) := by
  intro a b less
  unfold positiveEncodingUnits
  by_cases exponent : a / radix < b / radix
  · exact encodingUnits_lexicographic (Nat.mod_lt _ positive) exponent
  · have order := Nat.div_le_div_right (c := radix) less.le
    have same : a / radix = b / radix := by omega
    rw [same]
    apply encodingUnits_same_exponent
    have ha := Nat.div_add_mod a radix
    have hb := Nat.div_add_mod b radix
    rw [same] at ha
    omega

theorem powTwo_eq_zpow (exponent : Int) : powTwo exponent = (2 : Rat) ^ exponent := by
  cases exponent with
  | ofNat n => simp [powTwo]
  | negSucc n => simp [powTwo, zpow_negSucc]

theorem powTwo_add (a b : Int) : powTwo (a + b) = powTwo a * powTwo b := by
  simp only [powTwo_eq_zpow]
  exact zpow_add₀ (by decide) _ _

theorem powTwo_positive (exponent : Int) : 0 < powTwo exponent := by
  rw [powTwo_eq_zpow]
  positivity

/-- Finite positive decoding is a fixed positive scale of ordered integer units. -/
theorem finite_magnitude_units (width exponent fraction : Nat) :
    magnitudeValue width (if exponent = 0 then .SUBNORM fraction
      else .NORM fraction ((exponent : Int) - floatBias width)) =
      (encodingUnits (2 ^ fun_M width) exponent fraction : Rat) *
        powTwo (1 - (floatBias width : Int) - fun_M width) := by
  by_cases zero : exponent = 0
  · simp [zero, encodingUnits, magnitudeValue]
  · simp only [zero, if_false, encodingUnits, magnitudeValue]
    have split : (exponent : Int) - floatBias width - fun_M width =
        ((exponent - 1 : Nat) : Int) + (1 - (floatBias width : Int) - fun_M width) := by omega
    rw [split, powTwo_add]
    have natPower : powTwo ((exponent - 1 : Nat) : Int) = (2 : Rat) ^ (exponent - 1) := by
      rw [powTwo_eq_zpow]
      simp
    rw [natPower]
    push_cast
    ring

theorem positive_finite_value_32 (bits : Nat) (finite : bits < 2139095040) :
    finiteValue 32 (SpecExt.Builtins.floatOfBits 32 bits) =
      (positiveEncodingUnits 8388608 bits : Rat) * powTwo (-149) := by
  have encoding : SpecExt.Builtins.floatOfBits 32 bits =
      .POS (if bits / 8388608 = 0 then .SUBNORM (bits % 8388608)
        else .NORM (bits % 8388608) ((bits / 8388608 : Nat) - (127 : Int))) := by
    unfold SpecExt.Builtins.floatOfBits
    have exponent : bits / 8388608 % 256 = bits / 8388608 := Nat.mod_eq_of_lt (by omega)
    have sign : bits / 2147483648 % 2 = 0 := by omega
    change (if bits / 2147483648 % 2 = 0 then fN.POS _ else fN.NEG _) = _
    rw [sign]
    change fN.POS (if bits / 8388608 % 256 = 0 then .SUBNORM (bits % 8388608)
      else if bits / 8388608 % 256 = 255 then _ else .NORM (bits % 8388608) ((bits / 8388608 % 256 : Nat) - (127 : Int))) = _
    rw [exponent, if_neg (show bits / 8388608 ≠ 255 by omega)]
  rw [encoding]
  change magnitudeValue 32 _ = _
  exact finite_magnitude_units 32 (bits / 8388608) (bits % 8388608)

theorem positive_finite_value_64 (bits : Nat) (finite : bits < 9218868437227405312) :
    finiteValue 64 (SpecExt.Builtins.floatOfBits 64 bits) =
      (positiveEncodingUnits 4503599627370496 bits : Rat) * powTwo (-1074) := by
  have encoding : SpecExt.Builtins.floatOfBits 64 bits =
      .POS (if bits / 4503599627370496 = 0 then .SUBNORM (bits % 4503599627370496)
        else .NORM (bits % 4503599627370496) ((bits / 4503599627370496 : Nat) - (1023 : Int))) := by
    unfold SpecExt.Builtins.floatOfBits
    have exponent : bits / 4503599627370496 % 2048 = bits / 4503599627370496 := Nat.mod_eq_of_lt (by omega)
    have sign : bits / 9223372036854775808 % 2 = 0 := by omega
    change (if bits / 9223372036854775808 % 2 = 0 then fN.POS _ else fN.NEG _) = _
    rw [sign]
    change fN.POS (if bits / 4503599627370496 % 2048 = 0 then .SUBNORM (bits % 4503599627370496)
      else if bits / 4503599627370496 % 2048 = 2047 then _ else .NORM (bits % 4503599627370496) ((bits / 4503599627370496 % 2048 : Nat) - (1023 : Int))) = _
    rw [exponent, if_neg (show bits / 4503599627370496 ≠ 2047 by omega)]
  rw [encoding]
  change magnitudeValue 64 _ = _
  exact finite_magnitude_units 64 (bits / 4503599627370496) (bits % 4503599627370496)

theorem positive_finite_lt_32 (a b : Nat) (ha : a < 2139095040) (hb : b < 2139095040) :
    finiteValue 32 (SpecExt.Builtins.floatOfBits 32 a) <
      finiteValue 32 (SpecExt.Builtins.floatOfBits 32 b) ↔ a < b := by
  rw [positive_finite_value_32 a ha, positive_finite_value_32 b hb,
    mul_lt_mul_iff_left₀ (powTwo_positive (-149))]
  have same := (positiveEncodingUnits_strictMono 8388608 (by omega)).lt_iff_lt (a := a) (b := b)
  exact_mod_cast same

theorem positive_finite_eq_32 (a b : Nat) (ha : a < 2139095040) (hb : b < 2139095040) :
    finiteValue 32 (SpecExt.Builtins.floatOfBits 32 a) =
      finiteValue 32 (SpecExt.Builtins.floatOfBits 32 b) ↔ a = b := by
  rw [positive_finite_value_32 a ha, positive_finite_value_32 b hb,
    mul_right_cancel_iff_of_pos (powTwo_positive (-149))]
  have same := (positiveEncodingUnits_strictMono 8388608 (by omega)).injective.eq_iff (a := a) (b := b)
  exact_mod_cast same

theorem positive_finite_lt_64 (a b : Nat) (ha : a < 9218868437227405312) (hb : b < 9218868437227405312) :
    finiteValue 64 (SpecExt.Builtins.floatOfBits 64 a) <
      finiteValue 64 (SpecExt.Builtins.floatOfBits 64 b) ↔ a < b := by
  rw [positive_finite_value_64 a ha, positive_finite_value_64 b hb,
    mul_lt_mul_iff_left₀ (powTwo_positive (-1074))]
  have same := (positiveEncodingUnits_strictMono 4503599627370496 (by omega)).lt_iff_lt (a := a) (b := b)
  exact_mod_cast same

theorem positive_finite_eq_64 (a b : Nat) (ha : a < 9218868437227405312) (hb : b < 9218868437227405312) :
    finiteValue 64 (SpecExt.Builtins.floatOfBits 64 a) =
      finiteValue 64 (SpecExt.Builtins.floatOfBits 64 b) ↔ a = b := by
  rw [positive_finite_value_64 a ha, positive_finite_value_64 b hb,
    mul_right_cancel_iff_of_pos (powTwo_positive (-1074))]
  have same := (positiveEncodingUnits_strictMono 4503599627370496 (by omega)).injective.eq_iff (a := a) (b := b)
  exact_mod_cast same

end SpecExt.Builtins.Float
