import SpecExt.Builtins.Float.Compare
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
