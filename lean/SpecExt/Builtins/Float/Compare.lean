import SpecExt.Builtins.Float.Classify
import SpecExt.Builtins.Float.SignedOrder

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
