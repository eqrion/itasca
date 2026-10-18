import SpecExt.Builtins.Float.RawCompare
import SpecExt.Builtins.Float.Canonical

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
