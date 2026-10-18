import Exec.Interp.Numeric.Float.FloatCompareBits
import SpecExt.Builtins.Float.RawCompare

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins.Float

theorem compare_float_raw32 (op : U16) (a b : U64)
    (ha : a.val < 2 ^ 32) (hb : b.val < 2 ^ 32) (hop : op.val < 6) :
    runtime.interp.float.compare_float op a b 32#u32 ⦃ result =>
      result = rawCompare 2147483648 2139095040 op.val a.val b.val ⦄ := by
  have ma : (a &&& 2147483647#u64).val = a.val % 2147483648 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have mb : (b &&& 2147483647#u64).val = b.val % 2147483648 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 31
  unfold runtime.interp.float.compare_float
  simp only [if_true, Bind.bind, bind_ok]
  step as ⟨mask, maskValue⟩
  have exactMask : mask = 2147483647#u64 := by scalar_tac
  subst mask
  simp only [lift, bind_ok]
  by_cases na : a.val % 2147483648 > 2139095040
  · have condition : a &&& 2147483647#u64 > 2139095040#u64 := by
      simpa [UScalar.lt_equiv, ma] using na
    rw [if_pos condition]
    simp [rawCompare, na, UScalar.eq_equiv]
  have notNa : ¬ a &&& 2147483647#u64 > 2139095040#u64 := by
    simpa [UScalar.lt_equiv, ma] using na
  rw [if_neg notNa]
  by_cases nb : b.val % 2147483648 > 2139095040
  · have condition : b &&& 2147483647#u64 > 2139095040#u64 := by
      simpa [UScalar.lt_equiv, mb] using nb
    rw [if_pos condition]
    simp [rawCompare, nb, UScalar.eq_equiv]
  have notNb : ¬ b &&& 2147483647#u64 > 2139095040#u64 := by
    simpa [UScalar.lt_equiv, mb] using nb
  rw [if_neg notNb]
  have equalRun : (if a = b then Result.ok true else
      if a &&& 2147483647#u64 = 0#u64 then Result.ok (decide (b &&& 2147483647#u64 = 0#u64))
      else Result.ok false) = Result.ok (rawEqual 2147483648 a.val b.val) := by
    by_cases same : a.val = b.val <;> by_cases azero : a.val % 2147483648 = 0 <;>
      simp [rawEqual, UScalar.eq_equiv, ma, mb, same, azero]
  rw [equalRun]
  simp only [bind_ok]
  have lessRun : (if rawEqual 2147483648 a.val b.val then Result.ok false else
      runtime.interp.float.less_float_bits a b 2147483648#u64) ⦃ result =>
      result = rawLess 2147483648 a.val b.val ⦄ := by
    by_cases same : rawEqual 2147483648 a.val b.val = true
    · simp [same, rawLess]
    · simp only [same, if_false]
      apply WP.spec_mono (less_float_bits_32 a b ha hb)
      intro result effect
      simpa [rawLess, same] using effect
  step with lessRun as ⟨lt, effect⟩
  rw [effect]
  have choices : op = 0#u16 ∨ op = 1#u16 ∨ op = 2#u16 ∨ op = 3#u16 ∨ op = 4#u16 ∨ op = 5#u16 := by scalar_tac
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · with_unfolding_all change (Result.ok (rawEqual 2147483648 a.val b.val)) ⦃ result => result = rawCompare 2147483648 2139095040 0 a.val b.val ⦄
    simp [rawCompare, na, nb]
  · with_unfolding_all change (Result.ok (decide (¬ rawEqual 2147483648 a.val b.val = true))) ⦃ result => result = rawCompare 2147483648 2139095040 1 a.val b.val ⦄
    simp [rawCompare, na, nb]
  · with_unfolding_all change (Result.ok (rawLess 2147483648 a.val b.val)) ⦃ result => result = rawCompare 2147483648 2139095040 2 a.val b.val ⦄
    simp [rawCompare, na, nb]
  · with_unfolding_all change (if rawLess 2147483648 a.val b.val then Result.ok false else Result.ok (decide (¬ rawEqual 2147483648 a.val b.val = true))) ⦃ result => result = rawCompare 2147483648 2139095040 3 a.val b.val ⦄
    by_cases hlt : rawLess 2147483648 a.val b.val = true <;> simp [hlt, rawCompare, na, nb]
  · with_unfolding_all change (if rawLess 2147483648 a.val b.val then Result.ok true else Result.ok (rawEqual 2147483648 a.val b.val)) ⦃ result => result = rawCompare 2147483648 2139095040 4 a.val b.val ⦄
    by_cases hlt : rawLess 2147483648 a.val b.val = true <;> simp [hlt, rawCompare, na, nb]
  · with_unfolding_all change (Result.ok (decide (¬ rawLess 2147483648 a.val b.val = true))) ⦃ result => result = rawCompare 2147483648 2139095040 5 a.val b.val ⦄
    simp [rawCompare, na, nb]
theorem compare_float_raw64 (op : U16) (a b : U64)
    (ha : a.val < 2 ^ 64) (hb : b.val < 2 ^ 64) (hop : op.val < 6) :
    runtime.interp.float.compare_float op a b 64#u32 ⦃ result =>
      result = rawCompare 9223372036854775808 9218868437227405312 op.val a.val b.val ⦄ := by
  have ma : (a &&& 9223372036854775807#u64).val = a.val % 9223372036854775808 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 63
  have mb : (b &&& 9223372036854775807#u64).val = b.val % 9223372036854775808 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 63
  unfold runtime.interp.float.compare_float
  simp only [show ¬ (64#u32 = 32#u32) by decide, if_false, Bind.bind, bind_ok]
  step as ⟨mask, maskValue⟩
  have exactMask : mask = 9223372036854775807#u64 := by scalar_tac
  subst mask
  simp only [lift, bind_ok]
  by_cases na : a.val % 9223372036854775808 > 9218868437227405312
  · have condition : a &&& 9223372036854775807#u64 > 9218868437227405312#u64 := by
      simpa [UScalar.lt_equiv, ma] using na
    rw [if_pos condition]
    simp [rawCompare, na, UScalar.eq_equiv]
  have notNa : ¬ a &&& 9223372036854775807#u64 > 9218868437227405312#u64 := by
    simpa [UScalar.lt_equiv, ma] using na
  rw [if_neg notNa]
  by_cases nb : b.val % 9223372036854775808 > 9218868437227405312
  · have condition : b &&& 9223372036854775807#u64 > 9218868437227405312#u64 := by
      simpa [UScalar.lt_equiv, mb] using nb
    rw [if_pos condition]
    simp [rawCompare, nb, UScalar.eq_equiv]
  have notNb : ¬ b &&& 9223372036854775807#u64 > 9218868437227405312#u64 := by
    simpa [UScalar.lt_equiv, mb] using nb
  rw [if_neg notNb]
  have equalRun : (if a = b then Result.ok true else
      if a &&& 9223372036854775807#u64 = 0#u64 then Result.ok (decide (b &&& 9223372036854775807#u64 = 0#u64))
      else Result.ok false) = Result.ok (rawEqual 9223372036854775808 a.val b.val) := by
    by_cases same : a.val = b.val <;> by_cases azero : a.val % 9223372036854775808 = 0 <;>
      simp [rawEqual, UScalar.eq_equiv, ma, mb, same, azero]
  rw [equalRun]
  simp only [bind_ok]
  have lessRun : (if rawEqual 9223372036854775808 a.val b.val then Result.ok false else
      runtime.interp.float.less_float_bits a b 9223372036854775808#u64) ⦃ result =>
      result = rawLess 9223372036854775808 a.val b.val ⦄ := by
    by_cases same : rawEqual 9223372036854775808 a.val b.val = true
    · simp [same, rawLess]
    · simp only [same, if_false]
      apply WP.spec_mono (less_float_bits_64 a b ha hb)
      intro result effect
      simpa [rawLess, same] using effect
  step with lessRun as ⟨lt, effect⟩
  rw [effect]
  have choices : op = 0#u16 ∨ op = 1#u16 ∨ op = 2#u16 ∨ op = 3#u16 ∨ op = 4#u16 ∨ op = 5#u16 := by scalar_tac
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · with_unfolding_all change (Result.ok (rawEqual 9223372036854775808 a.val b.val)) ⦃ result => result = rawCompare 9223372036854775808 9218868437227405312 0 a.val b.val ⦄
    simp [rawCompare, na, nb]
  · with_unfolding_all change (Result.ok (decide (¬ rawEqual 9223372036854775808 a.val b.val = true))) ⦃ result => result = rawCompare 9223372036854775808 9218868437227405312 1 a.val b.val ⦄
    simp [rawCompare, na, nb]
  · with_unfolding_all change (Result.ok (rawLess 9223372036854775808 a.val b.val)) ⦃ result => result = rawCompare 9223372036854775808 9218868437227405312 2 a.val b.val ⦄
    simp [rawCompare, na, nb]
  · with_unfolding_all change (if rawLess 9223372036854775808 a.val b.val then Result.ok false else Result.ok (decide (¬ rawEqual 9223372036854775808 a.val b.val = true))) ⦃ result => result = rawCompare 9223372036854775808 9218868437227405312 3 a.val b.val ⦄
    by_cases hlt : rawLess 9223372036854775808 a.val b.val = true <;> simp [hlt, rawCompare, na, nb]
  · with_unfolding_all change (if rawLess 9223372036854775808 a.val b.val then Result.ok true else Result.ok (rawEqual 9223372036854775808 a.val b.val)) ⦃ result => result = rawCompare 9223372036854775808 9218868437227405312 4 a.val b.val ⦄
    by_cases hlt : rawLess 9223372036854775808 a.val b.val = true <;> simp [hlt, rawCompare, na, nb]
  · with_unfolding_all change (Result.ok (decide (¬ rawLess 9223372036854775808 a.val b.val = true))) ⦃ result => result = rawCompare 9223372036854775808 9218868437227405312 5 a.val b.val ⦄
    simp [rawCompare, na, nb]
end Exec.Interp
