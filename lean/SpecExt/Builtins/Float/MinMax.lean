import SpecExt.Builtins.Float.Sign
import SpecExt.Builtins.Examples
import Mathlib.Tactic

/-!
Sections, each formerly its own module: Storage, Order, Classify, SignedOrder, Compare, RawCompare, MinMax.
-/

/-! ## Storage -/

section

/-! Bit-list and little-endian byte-list float roundtrips, including both zeros,
infinities, and all well-formed NaN payloads. -/

namespace SpecExt.Builtins.Float

theorem fbits_roundtrip_32 (value : fN) (h : wf_fN 32 value) :
    inv_fbits_ 32 (fbits_ 32 value) = value := by
  unfold inv_fbits_ fbits_
  rw [integerBits_roundtrip (floatBits_lt_32 value h)]
  exact float_roundtrip_32 value h

theorem fbits_roundtrip_64 (value : fN) (h : wf_fN 64 value) :
    inv_fbits_ 64 (fbits_ 64 value) = value := by
  unfold inv_fbits_ fbits_
  rw [integerBits_roundtrip (floatBits_lt_64 value h)]
  exact float_roundtrip_64 value h

theorem fbytes_roundtrip_32 (value : fN) (h : wf_fN 32 value) :
    inv_fbytes_ 32 (fbytes_ 32 value) = value := by
  change floatOfBits 32 (integerOfBytes (integerBytes 4 (floatBits 32 value))) = value
  have hb : floatBits 32 value < 256 ^ 4 := floatBits_lt_32 value h
  rw [integerBytes_roundtrip hb]
  exact float_roundtrip_32 value h

theorem fbytes_roundtrip_64 (value : fN) (h : wf_fN 64 value) :
    inv_fbytes_ 64 (fbytes_ 64 value) = value := by
  change floatOfBits 64 (integerOfBytes (integerBytes 8 (floatBits 64 value))) = value
  have hb : floatBits 64 value < 256 ^ 8 := floatBits_lt_64 value h
  rw [integerBytes_roundtrip hb]
  exact float_roundtrip_64 value h

end SpecExt.Builtins.Float

end

/-! ## Order -/

section

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

end

/-! ## Classify -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem isInf_floatOfBits_32 (bits : Nat) :
    isInf (floatOfBits 32 bits) = decide (bits % 2147483648 = 2139095040) := by
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isInf, magnitude, beq_eq_decide] <;> omega

theorem isZero_floatOfBits_32 (bits : Nat) :
    isZero (floatOfBits 32 bits) = decide (bits % 2147483648 = 0) := by
  have decomposition : bits % 2147483648 = bits % 8388608 + 8388608 * (bits / 8388608 % 256) := by omega
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isZero, magnitude, beq_eq_decide]

theorem negative_floatOfBits_32 (bits : Nat) (bound : bits < 2 ^ 32) :
    negative (floatOfBits 32 bits) = decide (2147483648 ≤ bits) := by
  unfold floatOfBits
  change negative (if bits / 2147483648 % 2 = 0 then .POS _ else .NEG _) = _
  split <;> simp_all [negative] <;> omega

theorem finiteValue_abs_32 (bits : Nat) :
    finiteValue 32 (floatOfBits 32 (bits % 2147483648)) =
      magnitudeValue 32 (magnitude (floatOfBits 32 bits)) := by
  rw [floatOfBits_abs32]
  rfl

theorem finiteValue_signed_32 (bits : Nat) (bound : bits < 2 ^ 32) :
    finiteValue 32 (floatOfBits 32 bits) =
      if 2147483648 ≤ bits then -finiteValue 32 (floatOfBits 32 (bits % 2147483648))
      else finiteValue 32 (floatOfBits 32 (bits % 2147483648)) := by
  rw [finiteValue_abs_32]
  unfold finiteValue
  rw [negative_floatOfBits_32 bits bound]
  simp only [decide_eq_true_eq]

theorem isInf_floatOfBits_64 (bits : Nat) :
    isInf (floatOfBits 64 bits) = decide (bits % 9223372036854775808 = 9218868437227405312) := by
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isInf, magnitude, beq_eq_decide] <;> omega

theorem isZero_floatOfBits_64 (bits : Nat) :
    isZero (floatOfBits 64 bits) = decide (bits % 9223372036854775808 = 0) := by
  have decomposition : bits % 9223372036854775808 = bits % 4503599627370496 + 4503599627370496 * (bits / 4503599627370496 % 2048) := by omega
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isZero, magnitude, beq_eq_decide]

theorem negative_floatOfBits_64 (bits : Nat) (bound : bits < 2 ^ 64) :
    negative (floatOfBits 64 bits) = decide (9223372036854775808 ≤ bits) := by
  unfold floatOfBits
  change negative (if bits / 9223372036854775808 % 2 = 0 then .POS _ else .NEG _) = _
  split <;> simp_all [negative] <;> omega

theorem finiteValue_abs_64 (bits : Nat) :
    finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808)) =
      magnitudeValue 64 (magnitude (floatOfBits 64 bits)) := by
  rw [floatOfBits_abs64]
  rfl

theorem finiteValue_signed_64 (bits : Nat) (bound : bits < 2 ^ 64) :
    finiteValue 64 (floatOfBits 64 bits) =
      if 9223372036854775808 ≤ bits then -finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808))
      else finiteValue 64 (floatOfBits 64 (bits % 9223372036854775808)) := by
  rw [finiteValue_abs_64]
  unfold finiteValue
  rw [negative_floatOfBits_64 bits bound]
  simp only [decide_eq_true_eq]

end SpecExt.Builtins.Float

end

/-! ## SignedOrder -/

section

namespace SpecExt.Builtins.Float

theorem signed_values_eq (a b : Rat) (na nb : Bool) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if na then -a else a) = (if nb then -b else b) ↔
      (na = nb ∧ a = b) ∨ (a = 0 ∧ b = 0) := by
  cases na <;> cases nb <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false,
    if_true, false_and, true_and, false_or,
    neg_inj]
  all_goals constructor
  all_goals try { intro h; exact Or.inl h }
  all_goals try { rintro (h | ⟨rfl, rfl⟩); exact h; rfl }
  all_goals try { intro h; constructor <;> linarith }
  all_goals try { rintro ⟨rfl, rfl⟩; simp }

theorem signed_values_lt (a b : Rat) (na nb : Bool) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if na then -a else a) < (if nb then -b else b) ↔
      if na = nb then (if na then b < a else a < b)
      else na = true ∧ (a ≠ 0 ∨ b ≠ 0) := by
  cases na <;> cases nb <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false,
    if_true, false_and, true_and,
    neg_lt_neg_iff]
  · constructor
    · intro h; linarith
    · intro h; exact False.elim h
  · constructor
    · intro h
      by_contra zero
      simp only [not_or, not_not] at zero
      linarith [zero.1, zero.2]
    · rintro (h | h)
      · have positive : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
        linarith
      · have positive : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
        linarith
end SpecExt.Builtins.Float

end

/-! ## Compare -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem finite_bits_equal_32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (fa : a % 2147483648 < 2139095040) (fb : b % 2147483648 < 2139095040) :
    finiteValue 32 (floatOfBits 32 a) = finiteValue 32 (floatOfBits 32 b) ↔
      a = b ∨ (a % 2147483648 = 0 ∧ b % 2147483648 = 0) := by
  have zero : finiteValue 32 (floatOfBits 32 0) = 0 := by
    simp [finiteValue, floatOfBits, magnitude, negative, magnitudeValue]
  have nonnega : 0 ≤ finiteValue 32 (floatOfBits 32 (a % 2147483648)) := by
    rw [positive_finite_value_32 _ fa]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have nonnegb : 0 ≤ finiteValue 32 (floatOfBits 32 (b % 2147483648)) := by
    rw [positive_finite_value_32 _ fb]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have magnitudes := positive_finite_eq_32 _ _ fa fb
  have azero := positive_finite_eq_32 _ 0 fa (by omega)
  have bzero := positive_finite_eq_32 _ 0 fb (by omega)
  rw [zero] at azero bzero
  have signed := signed_values_eq _ _ (decide (2147483648 ≤ a)) (decide (2147483648 ≤ b)) nonnega nonnegb
  simp only [decide_eq_true_eq] at signed
  rw [finiteValue_signed_32 a ha, finiteValue_signed_32 b hb, signed, magnitudes, azero, bzero]
  by_cases sa : 2147483648 ≤ a <;> by_cases sb : 2147483648 ≤ b <;> simp [sa, sb] <;> omega

theorem finite_bits_equal_64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (fa : a % 9223372036854775808 < 9218868437227405312) (fb : b % 9223372036854775808 < 9218868437227405312) :
    finiteValue 64 (floatOfBits 64 a) = finiteValue 64 (floatOfBits 64 b) ↔
      a = b ∨ (a % 9223372036854775808 = 0 ∧ b % 9223372036854775808 = 0) := by
  have zero : finiteValue 64 (floatOfBits 64 0) = 0 := by
    simp [finiteValue, floatOfBits, magnitude, negative, magnitudeValue]
  have nonnega : 0 ≤ finiteValue 64 (floatOfBits 64 (a % 9223372036854775808)) := by
    rw [positive_finite_value_64 _ fa]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have nonnegb : 0 ≤ finiteValue 64 (floatOfBits 64 (b % 9223372036854775808)) := by
    rw [positive_finite_value_64 _ fb]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have magnitudes := positive_finite_eq_64 _ _ fa fb
  have azero := positive_finite_eq_64 _ 0 fa (by omega)
  have bzero := positive_finite_eq_64 _ 0 fb (by omega)
  rw [zero] at azero bzero
  have signed := signed_values_eq _ _ (decide (9223372036854775808 ≤ a)) (decide (9223372036854775808 ≤ b)) nonnega nonnegb
  simp only [decide_eq_true_eq] at signed
  rw [finiteValue_signed_64 a ha, finiteValue_signed_64 b hb, signed, magnitudes, azero, bzero]
  by_cases sa : 9223372036854775808 ≤ a <;> by_cases sb : 9223372036854775808 ≤ b <;> simp [sa, sb] <;> omega

theorem finite_bits_less_32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (fa : a % 2147483648 < 2139095040) (fb : b % 2147483648 < 2139095040) :
    finiteValue 32 (floatOfBits 32 a) < finiteValue 32 (floatOfBits 32 b) ↔
      if (2147483648 ≤ a ↔ 2147483648 ≤ b) then (if 2147483648 ≤ a then b < a else a < b)
      else 2147483648 ≤ a ∧ (a % 2147483648 ≠ 0 ∨ b % 2147483648 ≠ 0) := by
  have zero : finiteValue 32 (floatOfBits 32 0) = 0 := by
    simp [finiteValue, floatOfBits, magnitude, negative, magnitudeValue]
  have nonnega : 0 ≤ finiteValue 32 (floatOfBits 32 (a % 2147483648)) := by
    rw [positive_finite_value_32 _ fa]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have nonnegb : 0 ≤ finiteValue 32 (floatOfBits 32 (b % 2147483648)) := by
    rw [positive_finite_value_32 _ fb]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have increasing := positive_finite_lt_32 _ _ fa fb
  have decreasing := positive_finite_lt_32 _ _ fb fa
  have azero := positive_finite_eq_32 _ 0 fa (by omega)
  have bzero := positive_finite_eq_32 _ 0 fb (by omega)
  rw [zero] at azero bzero
  have signed := signed_values_lt _ _ (decide (2147483648 ≤ a)) (decide (2147483648 ≤ b)) nonnega nonnegb
  simp only [decide_eq_true_eq] at signed
  rw [finiteValue_signed_32 a ha, finiteValue_signed_32 b hb, signed]
  by_cases sa : 2147483648 ≤ a <;> by_cases sb : 2147483648 ≤ b <;>
    simp [sa, sb, increasing, decreasing, azero, bzero] <;> omega

theorem finite_bits_less_64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (fa : a % 9223372036854775808 < 9218868437227405312) (fb : b % 9223372036854775808 < 9218868437227405312) :
    finiteValue 64 (floatOfBits 64 a) < finiteValue 64 (floatOfBits 64 b) ↔
      if (9223372036854775808 ≤ a ↔ 9223372036854775808 ≤ b) then (if 9223372036854775808 ≤ a then b < a else a < b)
      else 9223372036854775808 ≤ a ∧ (a % 9223372036854775808 ≠ 0 ∨ b % 9223372036854775808 ≠ 0) := by
  have zero : finiteValue 64 (floatOfBits 64 0) = 0 := by
    simp [finiteValue, floatOfBits, magnitude, negative, magnitudeValue]
  have nonnega : 0 ≤ finiteValue 64 (floatOfBits 64 (a % 9223372036854775808)) := by
    rw [positive_finite_value_64 _ fa]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have nonnegb : 0 ≤ finiteValue 64 (floatOfBits 64 (b % 9223372036854775808)) := by
    rw [positive_finite_value_64 _ fb]
    exact mul_nonneg (Nat.cast_nonneg _) (powTwo_positive _).le
  have increasing := positive_finite_lt_64 _ _ fa fb
  have decreasing := positive_finite_lt_64 _ _ fb fa
  have azero := positive_finite_eq_64 _ 0 fa (by omega)
  have bzero := positive_finite_eq_64 _ 0 fb (by omega)
  rw [zero] at azero bzero
  have signed := signed_values_lt _ _ (decide (9223372036854775808 ≤ a)) (decide (9223372036854775808 ≤ b)) nonnega nonnegb
  simp only [decide_eq_true_eq] at signed
  rw [finiteValue_signed_64 a ha, finiteValue_signed_64 b hb, signed]
  by_cases sa : 9223372036854775808 ≤ a <;> by_cases sb : 9223372036854775808 ≤ b <;>
    simp [sa, sb, increasing, decreasing, azero, bzero] <;> omega

theorem floatOfBits_eq_32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    floatOfBits 32 a = floatOfBits 32 b ↔ a = b := by
  constructor
  · intro same
    have packed := congrArg (floatBits 32) same
    simpa only [float_bits_roundtrip_32 a ha, float_bits_roundtrip_32 b hb] using packed
  · intro same; subst b; rfl

theorem equal_floatOfBits_32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false
      else decide (a = b ∨ (a % 2147483648 = 0 ∧ b % 2147483648 = 0)) := by
  have decoded := floatOfBits_eq_32 a b ha hb
  by_cases na : a % 2147483648 > 2139095040
  · simp [equal, isNaN_floatOfBits_32, na]
  by_cases nb : b % 2147483648 > 2139095040
  · simp [equal, isNaN_floatOfBits_32, nb]
  by_cases ia : a % 2147483648 = 2139095040
  · have nonzero : a % 2147483648 ≠ 0 := by omega
    simp [equal, isNaN_floatOfBits_32, isInf_floatOfBits_32, na, nb, ia,
      nonzero, beq_eq_decide, decoded]
  by_cases ib : b % 2147483648 = 2139095040
  · have nonzero : b % 2147483648 ≠ 0 := by omega
    simp [equal, isNaN_floatOfBits_32, isInf_floatOfBits_32, na, nb, ib,
      nonzero, beq_eq_decide, decoded]
  · have finite := finite_bits_equal_32 a b ha hb (by omega) (by omega)
    simp [equal, isNaN_floatOfBits_32, isInf_floatOfBits_32, na, nb, ia, ib,
      beq_eq_decide, finite]

theorem floatOfBits_eq_64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    floatOfBits 64 a = floatOfBits 64 b ↔ a = b := by
  constructor
  · intro same
    have packed := congrArg (floatBits 64) same
    simpa only [float_bits_roundtrip_64 a ha, float_bits_roundtrip_64 b hb] using packed
  · intro same; subst b; rfl

theorem equal_floatOfBits_64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false
      else decide (a = b ∨ (a % 9223372036854775808 = 0 ∧ b % 9223372036854775808 = 0)) := by
  have decoded := floatOfBits_eq_64 a b ha hb
  by_cases na : a % 9223372036854775808 > 9218868437227405312
  · simp [equal, isNaN_floatOfBits_64, na]
  by_cases nb : b % 9223372036854775808 > 9218868437227405312
  · simp [equal, isNaN_floatOfBits_64, nb]
  by_cases ia : a % 9223372036854775808 = 9218868437227405312
  · have nonzero : a % 9223372036854775808 ≠ 0 := by omega
    simp [equal, isNaN_floatOfBits_64, isInf_floatOfBits_64, na, nb, ia,
      nonzero, beq_eq_decide, decoded]
  by_cases ib : b % 9223372036854775808 = 9218868437227405312
  · have nonzero : b % 9223372036854775808 ≠ 0 := by omega
    simp [equal, isNaN_floatOfBits_64, isInf_floatOfBits_64, na, nb, ib,
      nonzero, beq_eq_decide, decoded]
  · have finite := finite_bits_equal_64 a b ha hb (by omega) (by omega)
    simp [equal, isNaN_floatOfBits_64, isInf_floatOfBits_64, na, nb, ia, ib,
      beq_eq_decide, finite]

theorem less_floatOfBits_32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false
      else if a = b ∨ (a % 2147483648 = 0 ∧ b % 2147483648 = 0) then false
      else if (2147483648 ≤ a ↔ 2147483648 ≤ b) then
        if 2147483648 ≤ a then decide (b < a) else decide (a < b)
      else decide (2147483648 ≤ a) := by
  by_cases na : a % 2147483648 > 2139095040
  · simp [less, isNaN_floatOfBits_32, na]
  by_cases nb : b % 2147483648 > 2139095040
  · simp [less, isNaN_floatOfBits_32, nb]
  by_cases ia : a % 2147483648 = 2139095040
  · by_cases ib : b % 2147483648 = 2139095040 <;>
      by_cases sa : 2147483648 ≤ a <;> by_cases sb : 2147483648 ≤ b <;>
      simp [less, isNaN_floatOfBits_32, isInf_floatOfBits_32, negative_floatOfBits_32 a ha,
        negative_floatOfBits_32 b hb, na, nb, ia, ib, sa, sb] <;>
      (try split_ifs) <;> simp_all <;> omega
  by_cases ib : b % 2147483648 = 2139095040
  · by_cases sa : 2147483648 ≤ a <;> by_cases sb : 2147483648 ≤ b <;>
      simp [less, isNaN_floatOfBits_32, isInf_floatOfBits_32, negative_floatOfBits_32 a ha,
        negative_floatOfBits_32 b hb, na, nb, ia, ib, sa, sb] <;>
      (try split_ifs) <;> simp_all <;> omega
  · have finite := finite_bits_less_32 a b ha hb (by omega) (by omega)
    by_cases sa : 2147483648 ≤ a <;> by_cases sb : 2147483648 ≤ b <;>
      simp [less, isNaN_floatOfBits_32, isInf_floatOfBits_32, negative_floatOfBits_32 a ha,
        negative_floatOfBits_32 b hb, na, nb, ia, ib, sa, sb, finite] <;>
      (try split_ifs) <;> simp_all <;> omega

theorem less_floatOfBits_64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false
      else if a = b ∨ (a % 9223372036854775808 = 0 ∧ b % 9223372036854775808 = 0) then false
      else if (9223372036854775808 ≤ a ↔ 9223372036854775808 ≤ b) then
        if 9223372036854775808 ≤ a then decide (b < a) else decide (a < b)
      else decide (9223372036854775808 ≤ a) := by
  by_cases na : a % 9223372036854775808 > 9218868437227405312
  · simp [less, isNaN_floatOfBits_64, na]
  by_cases nb : b % 9223372036854775808 > 9218868437227405312
  · simp [less, isNaN_floatOfBits_64, nb]
  by_cases ia : a % 9223372036854775808 = 9218868437227405312
  · by_cases ib : b % 9223372036854775808 = 9218868437227405312 <;>
      by_cases sa : 9223372036854775808 ≤ a <;> by_cases sb : 9223372036854775808 ≤ b <;>
      simp [less, isNaN_floatOfBits_64, isInf_floatOfBits_64, negative_floatOfBits_64 a ha,
        negative_floatOfBits_64 b hb, na, nb, ia, ib, sa, sb] <;>
      (try split_ifs) <;> simp_all <;> omega
  by_cases ib : b % 9223372036854775808 = 9218868437227405312
  · by_cases sa : 9223372036854775808 ≤ a <;> by_cases sb : 9223372036854775808 ≤ b <;>
      simp [less, isNaN_floatOfBits_64, isInf_floatOfBits_64, negative_floatOfBits_64 a ha,
        negative_floatOfBits_64 b hb, na, nb, ia, ib, sa, sb] <;>
      (try split_ifs) <;> simp_all <;> omega
  · have finite := finite_bits_less_64 a b ha hb (by omega) (by omega)
    by_cases sa : 9223372036854775808 ≤ a <;> by_cases sb : 9223372036854775808 ≤ b <;>
      simp [less, isNaN_floatOfBits_64, isInf_floatOfBits_64, negative_floatOfBits_64 a ha,
        negative_floatOfBits_64 b hb, na, nb, ia, ib, sa, sb, finite] <;>
      (try split_ifs) <;> simp_all <;> omega

end SpecExt.Builtins.Float

end

/-! ## RawCompare -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

def rawEqual (sign a b : Nat) : Bool := decide (a = b ∨ (a % sign = 0 ∧ b % sign = 0))
def rawLess (sign a b : Nat) : Bool :=
  if rawEqual sign a b then false
  else if (sign ≤ a ↔ sign ≤ b) then if sign ≤ a then decide (b < a) else decide (a < b)
  else decide (sign ≤ a)

def rawCompare (sign infinity op a b : Nat) : Bool :=
  if a % sign > infinity ∨ b % sign > infinity then decide (op = 1)
  else
    let eq := rawEqual sign a b
    let lt := rawLess sign a b
    if op = 0 then eq else if op = 1 then !eq else if op = 2 then lt
    else if op = 3 then !lt && !eq else if op = 4 then lt || eq else !lt

end SpecExt.Builtins.Float
namespace SpecExt.Builtins.Float

theorem rawEqual_comm (sign a b : Nat) : rawEqual sign a b = rawEqual sign b a := by
  simp [rawEqual, eq_comm, and_comm]

theorem rawLess_swap (sign a b : Nat) :
    rawLess sign b a = (!rawLess sign a b && !rawEqual sign a b) := by
  by_cases eq : a = b ∨ (a % sign = 0 ∧ b % sign = 0)
  · have swapped : b = a ∨ (b % sign = 0 ∧ a % sign = 0) := by tauto
    simp [rawLess, rawEqual, eq, swapped]
  · have swapped : ¬ (b = a ∨ (b % sign = 0 ∧ a % sign = 0)) := by tauto
    by_cases sa : sign ≤ a <;> by_cases sb : sign ≤ b <;>
      by_cases ab : a < b <;> by_cases ba : b < a <;>
      simp [rawLess, rawEqual, eq, swapped, sa, sb, ab, ba] <;> omega

theorem rawLess_equal_exclusive (sign a b : Nat) :
    (rawLess sign a b && rawEqual sign a b) = false := by
  unfold rawLess
  split <;> simp_all

theorem rawLess_swap_or_equal (sign a b : Nat) :
    (rawLess sign b a || rawEqual sign b a) = !rawLess sign a b := by
  rw [rawLess_swap, rawEqual_comm sign b a]
  have exclusive := rawLess_equal_exclusive sign a b
  cases hl : rawLess sign a b <;> cases he : rawEqual sign a b <;> simp_all
end SpecExt.Builtins.Float

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem rawCompare_eq32 (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    rawCompare 2147483648 2139095040 0 a b = (equal 32 (floatOfBits 32 a) (floatOfBits 32 b)) := by
  have eqab : equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 a b := by
    simpa [rawEqual] using equal_floatOfBits_32 a b ha hb
  have eqba : equal 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_32 b a hb ha
  have ltab : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_32 a b ha hb
  have ltba : less 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_32 b a hb ha
  by_cases nan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 2147483648 a b, rawLess_swap 2147483648 a b]

theorem rawCompare_ne32 (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    rawCompare 2147483648 2139095040 1 a b = (!equal 32 (floatOfBits 32 a) (floatOfBits 32 b)) := by
  have eqab : equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 a b := by
    simpa [rawEqual] using equal_floatOfBits_32 a b ha hb
  have eqba : equal 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_32 b a hb ha
  have ltab : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_32 a b ha hb
  have ltba : less 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_32 b a hb ha
  by_cases nan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 2147483648 a b, rawLess_swap 2147483648 a b]

theorem rawCompare_lt32 (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    rawCompare 2147483648 2139095040 2 a b = (less 32 (floatOfBits 32 a) (floatOfBits 32 b)) := by
  have eqab : equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 a b := by
    simpa [rawEqual] using equal_floatOfBits_32 a b ha hb
  have eqba : equal 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_32 b a hb ha
  have ltab : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_32 a b ha hb
  have ltba : less 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_32 b a hb ha
  by_cases nan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 2147483648 a b, rawLess_swap 2147483648 a b]

theorem rawCompare_gt32 (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    rawCompare 2147483648 2139095040 3 a b = (less 32 (floatOfBits 32 b) (floatOfBits 32 a)) := by
  have eqab : equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 a b := by
    simpa [rawEqual] using equal_floatOfBits_32 a b ha hb
  have eqba : equal 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_32 b a hb ha
  have ltab : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_32 a b ha hb
  have ltba : less 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_32 b a hb ha
  by_cases nan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 2147483648 a b, rawLess_swap 2147483648 a b]

theorem rawCompare_le32 (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    rawCompare 2147483648 2139095040 4 a b = (less 32 (floatOfBits 32 a) (floatOfBits 32 b) || equal 32 (floatOfBits 32 a) (floatOfBits 32 b)) := by
  have eqab : equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 a b := by
    simpa [rawEqual] using equal_floatOfBits_32 a b ha hb
  have eqba : equal 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_32 b a hb ha
  have ltab : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_32 a b ha hb
  have ltba : less 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_32 b a hb ha
  by_cases nan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 2147483648 a b, rawLess_swap 2147483648 a b]

theorem rawCompare_ge32 (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    rawCompare 2147483648 2139095040 5 a b = (less 32 (floatOfBits 32 b) (floatOfBits 32 a) || equal 32 (floatOfBits 32 b) (floatOfBits 32 a)) := by
  have eqab : equal 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 a b := by
    simpa [rawEqual] using equal_floatOfBits_32 a b ha hb
  have eqba : equal 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawEqual 2147483648 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_32 b a hb ha
  have ltab : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_32 a b ha hb
  have ltba : less 32 (floatOfBits 32 b) (floatOfBits 32 a) =
      if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then false else rawLess 2147483648 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_32 b a hb ha
  by_cases nan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 2147483648 a b]

theorem rawCompare_eq64 (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    rawCompare 9223372036854775808 9218868437227405312 0 a b = (equal 64 (floatOfBits 64 a) (floatOfBits 64 b)) := by
  have eqab : equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 a b := by
    simpa [rawEqual] using equal_floatOfBits_64 a b ha hb
  have eqba : equal 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_64 b a hb ha
  have ltab : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_64 a b ha hb
  have ltba : less 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_64 b a hb ha
  by_cases nan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 9223372036854775808 a b, rawLess_swap 9223372036854775808 a b]

theorem rawCompare_ne64 (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    rawCompare 9223372036854775808 9218868437227405312 1 a b = (!equal 64 (floatOfBits 64 a) (floatOfBits 64 b)) := by
  have eqab : equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 a b := by
    simpa [rawEqual] using equal_floatOfBits_64 a b ha hb
  have eqba : equal 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_64 b a hb ha
  have ltab : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_64 a b ha hb
  have ltba : less 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_64 b a hb ha
  by_cases nan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 9223372036854775808 a b, rawLess_swap 9223372036854775808 a b]

theorem rawCompare_lt64 (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    rawCompare 9223372036854775808 9218868437227405312 2 a b = (less 64 (floatOfBits 64 a) (floatOfBits 64 b)) := by
  have eqab : equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 a b := by
    simpa [rawEqual] using equal_floatOfBits_64 a b ha hb
  have eqba : equal 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_64 b a hb ha
  have ltab : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_64 a b ha hb
  have ltba : less 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_64 b a hb ha
  by_cases nan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 9223372036854775808 a b, rawLess_swap 9223372036854775808 a b]

theorem rawCompare_gt64 (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    rawCompare 9223372036854775808 9218868437227405312 3 a b = (less 64 (floatOfBits 64 b) (floatOfBits 64 a)) := by
  have eqab : equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 a b := by
    simpa [rawEqual] using equal_floatOfBits_64 a b ha hb
  have eqba : equal 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_64 b a hb ha
  have ltab : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_64 a b ha hb
  have ltba : less 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_64 b a hb ha
  by_cases nan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 9223372036854775808 a b, rawLess_swap 9223372036854775808 a b]

theorem rawCompare_le64 (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    rawCompare 9223372036854775808 9218868437227405312 4 a b = (less 64 (floatOfBits 64 a) (floatOfBits 64 b) || equal 64 (floatOfBits 64 a) (floatOfBits 64 b)) := by
  have eqab : equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 a b := by
    simpa [rawEqual] using equal_floatOfBits_64 a b ha hb
  have eqba : equal 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_64 b a hb ha
  have ltab : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_64 a b ha hb
  have ltba : less 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_64 b a hb ha
  by_cases nan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 9223372036854775808 a b, rawLess_swap 9223372036854775808 a b]

theorem rawCompare_ge64 (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    rawCompare 9223372036854775808 9218868437227405312 5 a b = (less 64 (floatOfBits 64 b) (floatOfBits 64 a) || equal 64 (floatOfBits 64 b) (floatOfBits 64 a)) := by
  have eqab : equal 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 a b := by
    simpa [rawEqual] using equal_floatOfBits_64 a b ha hb
  have eqba : equal 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawEqual 9223372036854775808 b a := by
    simpa [rawEqual, or_comm] using equal_floatOfBits_64 b a hb ha
  have ltab : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 a b := by
    simpa [rawEqual, rawLess] using less_floatOfBits_64 a b ha hb
  have ltba : less 64 (floatOfBits 64 b) (floatOfBits 64 a) =
      if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then false else rawLess 9223372036854775808 b a := by
    simpa [rawEqual, rawLess, or_comm] using less_floatOfBits_64 b a hb ha
  by_cases nan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  all_goals simp [rawCompare, eqab, eqba, ltab, ltba, nan,
    rawLess_swap_or_equal 9223372036854775808 a b]

end SpecExt.Builtins.Float

end

/-! ## MinMax -/

section

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem raw_min32_sound (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    floatOfBits 32 (if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then 2143289344
      else if rawEqual 2147483648 a b then a ||| b else if rawLess 2147483648 a b then a else b) ∈
      fmin_ 32 (floatOfBits 32 a) (floatOfBits 32 b) := by
  have canonical : floatOfBits 32 2143289344 = fN.POS (.NAN (canon_ 32)) := by decide +kernel
  have less : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      rawCompare 2147483648 2139095040 2 a b := (rawCompare_lt32 a b ha hb).symm
  unfold fmin_
  rw [isNaN_floatOfBits_32, isNaN_floatOfBits_32]
  by_cases hn : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  · simp only [hn, if_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [canonical]
    exact positive_canonical_mem_nans 32 _ (by decide)
  · have nans : (decide (a % 2147483648 > 2139095040) || decide (b % 2147483648 > 2139095040)) = false := by simp_all
    rw [nans]
    simp only [Bool.false_eq_true, ↓reduceIte, hn]
    rw [isZero_floatOfBits_32, isZero_floatOfBits_32]
    by_cases hz : a % 2147483648 = 0 ∧ b % 2147483648 = 0
    · have az : a = 0 ∨ a = 2147483648 := by omega
      have bz : b = 0 ∨ b = 2147483648 := by omega
      rcases az with rfl | rfl <;> rcases bz with rfl | rfl <;> decide +kernel
    · have zeros : (decide (a % 2147483648 = 0) && decide (b % 2147483648 = 0)) = false := by simp_all
      rw [zeros]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      by_cases same : a = b
      · subst b
        simp [rawEqual, rawLess, rawCompare, hn, less]
      · have eqfalse : rawEqual 2147483648 a b = false := by simp [rawEqual, same, hz]
        rw [eqfalse]
        simp only [Bool.false_eq_true, ↓reduceIte, less, rawCompare, hn]
        split <;> simp_all

theorem raw_max32_sound (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    floatOfBits 32 (if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then 2143289344
      else if rawEqual 2147483648 a b then a &&& b else if rawLess 2147483648 a b then b else a) ∈
      fmax_ 32 (floatOfBits 32 a) (floatOfBits 32 b) := by
  have canonical : floatOfBits 32 2143289344 = fN.POS (.NAN (canon_ 32)) := by decide +kernel
  have less : less 32 (floatOfBits 32 a) (floatOfBits 32 b) =
      rawCompare 2147483648 2139095040 2 a b := (rawCompare_lt32 a b ha hb).symm
  unfold fmax_
  rw [isNaN_floatOfBits_32, isNaN_floatOfBits_32]
  by_cases hn : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040
  · simp only [hn, if_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [canonical]
    exact positive_canonical_mem_nans 32 _ (by decide)
  · have nans : (decide (a % 2147483648 > 2139095040) || decide (b % 2147483648 > 2139095040)) = false := by simp_all
    rw [nans]
    simp only [Bool.false_eq_true, ↓reduceIte, hn]
    rw [isZero_floatOfBits_32, isZero_floatOfBits_32]
    by_cases hz : a % 2147483648 = 0 ∧ b % 2147483648 = 0
    · have az : a = 0 ∨ a = 2147483648 := by omega
      have bz : b = 0 ∨ b = 2147483648 := by omega
      rcases az with rfl | rfl <;> rcases bz with rfl | rfl <;> decide +kernel
    · have zeros : (decide (a % 2147483648 = 0) && decide (b % 2147483648 = 0)) = false := by simp_all
      rw [zeros]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      by_cases same : a = b
      · subst b
        simp [rawEqual, rawLess, rawCompare, hn, less]
      · have eqfalse : rawEqual 2147483648 a b = false := by simp [rawEqual, same, hz]
        rw [eqfalse]
        simp only [Bool.false_eq_true, ↓reduceIte, less, rawCompare, hn]
        split <;> simp_all

theorem raw_min64_sound (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    floatOfBits 64 (if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then 9221120237041090560
      else if rawEqual 9223372036854775808 a b then a ||| b else if rawLess 9223372036854775808 a b then a else b) ∈
      fmin_ 64 (floatOfBits 64 a) (floatOfBits 64 b) := by
  have canonical : floatOfBits 64 9221120237041090560 = fN.POS (.NAN (canon_ 64)) := by decide +kernel
  have less : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      rawCompare 9223372036854775808 9218868437227405312 2 a b := (rawCompare_lt64 a b ha hb).symm
  unfold fmin_
  rw [isNaN_floatOfBits_64, isNaN_floatOfBits_64]
  by_cases hn : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  · simp only [hn, if_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [canonical]
    exact positive_canonical_mem_nans 64 _ (by decide)
  · have nans : (decide (a % 9223372036854775808 > 9218868437227405312) || decide (b % 9223372036854775808 > 9218868437227405312)) = false := by simp_all
    rw [nans]
    simp only [Bool.false_eq_true, ↓reduceIte, hn]
    rw [isZero_floatOfBits_64, isZero_floatOfBits_64]
    by_cases hz : a % 9223372036854775808 = 0 ∧ b % 9223372036854775808 = 0
    · have az : a = 0 ∨ a = 9223372036854775808 := by omega
      have bz : b = 0 ∨ b = 9223372036854775808 := by omega
      rcases az with rfl | rfl <;> rcases bz with rfl | rfl <;> decide +kernel
    · have zeros : (decide (a % 9223372036854775808 = 0) && decide (b % 9223372036854775808 = 0)) = false := by simp_all
      rw [zeros]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      by_cases same : a = b
      · subst b
        simp [rawEqual, rawLess, rawCompare, hn, less]
      · have eqfalse : rawEqual 9223372036854775808 a b = false := by simp [rawEqual, same, hz]
        rw [eqfalse]
        simp only [Bool.false_eq_true, ↓reduceIte, less, rawCompare, hn]
        split <;> simp_all

theorem raw_max64_sound (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    floatOfBits 64 (if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then 9221120237041090560
      else if rawEqual 9223372036854775808 a b then a &&& b else if rawLess 9223372036854775808 a b then b else a) ∈
      fmax_ 64 (floatOfBits 64 a) (floatOfBits 64 b) := by
  have canonical : floatOfBits 64 9221120237041090560 = fN.POS (.NAN (canon_ 64)) := by decide +kernel
  have less : less 64 (floatOfBits 64 a) (floatOfBits 64 b) =
      rawCompare 9223372036854775808 9218868437227405312 2 a b := (rawCompare_lt64 a b ha hb).symm
  unfold fmax_
  rw [isNaN_floatOfBits_64, isNaN_floatOfBits_64]
  by_cases hn : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312
  · simp only [hn, if_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [canonical]
    exact positive_canonical_mem_nans 64 _ (by decide)
  · have nans : (decide (a % 9223372036854775808 > 9218868437227405312) || decide (b % 9223372036854775808 > 9218868437227405312)) = false := by simp_all
    rw [nans]
    simp only [Bool.false_eq_true, ↓reduceIte, hn]
    rw [isZero_floatOfBits_64, isZero_floatOfBits_64]
    by_cases hz : a % 9223372036854775808 = 0 ∧ b % 9223372036854775808 = 0
    · have az : a = 0 ∨ a = 9223372036854775808 := by omega
      have bz : b = 0 ∨ b = 9223372036854775808 := by omega
      rcases az with rfl | rfl <;> rcases bz with rfl | rfl <;> decide +kernel
    · have zeros : (decide (a % 9223372036854775808 = 0) && decide (b % 9223372036854775808 = 0)) = false := by simp_all
      rw [zeros]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      by_cases same : a = b
      · subst b
        simp [rawEqual, rawLess, rawCompare, hn, less]
      · have eqfalse : rawEqual 9223372036854775808 a b = false := by simp [rawEqual, same, hz]
        rw [eqfalse]
        simp only [Bool.false_eq_true, ↓reduceIte, less, rawCompare, hn]
        split <;> simp_all

end SpecExt.Builtins.Float

end
