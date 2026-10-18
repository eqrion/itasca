import SpecExt.Builtins.Rotations
import Mathlib.Data.Nat.Log

namespace SpecExt.Builtins

/-- Exposing the low bit reconciles the prose's big-endian list with Rust's
low-bit recurrences for population and trailing-zero counts. -/
theorem integerBits_lsb (width value : Nat) :
    integerBits (width + 1) value = integerBits width (value / 2) ++ [.mk_bit (value % 2)] := by
  induction width with
  | zero => simp [integerBits]
  | succ width ih =>
    simp only [integerBits, List.cons_append, ← Nat.div_div_eq_div_mul, ih]
    congr 2
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

theorem population_append (left right : List bit) :
    population (left ++ right) = population left + population right := by
  induction left with
  | nil => simp [population]
  | cons value rest ih => cases value; simp [population, ih, Nat.add_assoc]

theorem leadingZeros_zero (width : Nat) : leadingZeros (integerBits width 0) = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [integerBits, leadingZeros, ih, Nat.add_comm]

/-- The leading-zero list definition is the usual width-minus-log formula. -/
theorem leadingZeros_bits (width value : Nat) (bounded : value < 2 ^ width) :
    leadingZeros (integerBits width value) = if value = 0 then width else width - Nat.log 2 value - 1 := by
  by_cases zero : value = 0
  · subst value; simp [leadingZeros_zero]
  · simp only [zero, if_false]
    induction width with
    | zero => simp at bounded; contradiction
    | succ width ih =>
      by_cases lower : value < 2 ^ width
      · have digit : value / 2 ^ width % 2 = 0 := by simp [Nat.div_eq_of_lt lower]
        have logarithm : Nat.log 2 value < width := Nat.log_lt_of_lt_pow zero lower
        simp only [integerBits, digit, leadingZeros, ih lower]
        omega
      · have power : 2 ^ (width + 1) = 2 ^ width * 2 := pow_succ _ _
        have digit : value / 2 ^ width = 1 := by
          apply Nat.div_eq_of_lt_le
          · omega
          · omega
        have logarithm : Nat.log 2 value = width := Nat.log_eq_of_pow_le_of_lt_pow (by omega) bounded
        simp only [integerBits, digit, show 1 % 2 = 1 from rfl, leadingZeros, logarithm]
        omega

theorem leadingZeros_le_length (bits : List bit) : leadingZeros bits ≤ bits.length := by
  induction bits with
  | nil => simp [leadingZeros]
  | cons value rest ih =>
    cases value with
    | mk_bit value => cases value <;> simp [leadingZeros] <;> omega

theorem population_bits_le (width value : Nat) : population (integerBits width value) ≤ width := by
  induction width generalizing value with
  | zero => simp [integerBits, population]
  | succ width ih =>
    rw [integerBits_lsb, population_append]
    have prior := ih (value / 2)
    have digit := Nat.mod_lt value (by decide : 0 < 2)
    simp only [population, Nat.add_zero]
    omega

end SpecExt.Builtins
