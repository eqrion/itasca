import Itasca.Runtime.Interp.Numeric.Float
import WebAssembly.Builtins.Float.Comparison
import WebAssembly.Builtins.Float.Conversion
import Itasca.Runtime.Spec.PrimitiveOperations

open WebAssembly

/-!
Proofs for Runtime / Interp / Numeric / Float.

This module collects ComparisonAndScalarOperations, SourceRelations.
Each section documents its contracts and consumers.
-/

/-! ## ComparisonAndScalarOperations -/

section

/-!
# Comparison And Scalar Operations

Floating-point comparisons, conversions and scalar operations agree with their source numeric relations.
-/

/-! ## FloatCompareBits -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem float_sign_mask_32 (bits : U64) (bound : bits.val < 2 ^ 32) :
    bits &&& 2147483648#u64 = if 2147483648 ≤ bits.val then 2147483648#u64 else 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change bits.val &&& 2^31 = _
  rw [Nat.and_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have quotient : bits.val / 2147483648 % 2 = if 2147483648 ≤ bits.val then 1 else 0 := by
    split <;> omega
  simp only [Nat.one_and_eq_mod_two, quotient]
  split <;> rfl

theorem less_float_bits_32 (a b : U64)
    (ha : a.val < 2 ^ 32) (hb : b.val < 2 ^ 32) :
    runtime.interp.float.less_float_bits a b 2147483648#u64 ⦃ result =>
      result = if (2147483648 ≤ a.val ↔ 2147483648 ≤ b.val) then
        if 2147483648 ≤ a.val then decide (b.val < a.val) else decide (a.val < b.val)
      else decide (2147483648 ≤ a.val) ⦄ := by
  unfold runtime.interp.float.less_float_bits
  simp only [lift, bind_ok]
  rw [float_sign_mask_32 a ha, float_sign_mask_32 b hb]
  by_cases sa : 2147483648 ≤ a.val <;> by_cases sb : 2147483648 ≤ b.val <;>
    simp [sa, sb, UScalar.lt_equiv]

theorem float_sign_mask_64 (bits : U64) (bound : bits.val < 2 ^ 64) :
    bits &&& 9223372036854775808#u64 = if 9223372036854775808 ≤ bits.val then 9223372036854775808#u64 else 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.val_and]
  change bits.val &&& 2^63 = _
  rw [Nat.and_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have quotient : bits.val / 9223372036854775808 % 2 = if 9223372036854775808 ≤ bits.val then 1 else 0 := by
    split <;> omega
  simp only [Nat.one_and_eq_mod_two, quotient]
  split <;> rfl

theorem less_float_bits_64 (a b : U64)
    (ha : a.val < 2 ^ 64) (hb : b.val < 2 ^ 64) :
    runtime.interp.float.less_float_bits a b 9223372036854775808#u64 ⦃ result =>
      result = if (9223372036854775808 ≤ a.val ↔ 9223372036854775808 ≤ b.val) then
        if 9223372036854775808 ≤ a.val then decide (b.val < a.val) else decide (a.val < b.val)
      else decide (9223372036854775808 ≤ a.val) ⦄ := by
  unfold runtime.interp.float.less_float_bits
  simp only [lift, bind_ok]
  rw [float_sign_mask_64 a ha, float_sign_mask_64 b hb]
  by_cases sa : 9223372036854775808 ≤ a.val <;> by_cases sb : 9223372036854775808 ≤ b.val <;>
    simp [sa, sb, UScalar.lt_equiv]

end Itasca.Interp

end

/-! ## FloatCompare -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly.Builtins.Float

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
end Itasca.Interp

end

/-! ## FloatMinMax -/

section

set_option maxHeartbeats 1000000
namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly.Builtins WebAssembly.Builtins.Float

@[step] theorem binary32_min_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U32) :
    runtime.interp.float.binary32 ops 4#u16 a b ⦃ result => floatOfBits 32 result.val ∈ fmin_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  have mask (x : U32) : (x &&& 2147483647#u32).val = x.val % 2147483648 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 31
  unfold runtime.interp.float.binary32
  with_unfolding_all change (lift (a &&& 2147483647#u32) >>= fun am =>
    if am > 2139095040#u32 then Result.ok 2143289344#u32 else
    lift (b &&& 2147483647#u32) >>= fun bm =>
    if bm > 2139095040#u32 then Result.ok 2143289344#u32 else
    lift (UScalar.cast .U64 a) >>= fun av => lift (UScalar.cast .U64 b) >>= fun bv =>
    runtime.interp.float.compare_float 0#u16 av bv 32#u32 >>= fun eq =>
    if eq then (if 4#u16 = 4#u16 then Result.ok (a ||| b) else Result.ok (a &&& b)) else
    lift (UScalar.cast .U64 a) >>= fun av => lift (UScalar.cast .U64 b) >>= fun bv =>
    runtime.interp.float.compare_float 2#u16 av bv 32#u32 >>= fun lt =>
    if lt = (4#u16 = 4#u16) then Result.ok a else Result.ok b) ⦃ result => floatOfBits 32 result.val ∈ fmin_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  simp [lift, Bind.bind, bind_ok, UScalar.lt_equiv, mask]
  have pure := raw_min32_sound a.val b.val (by scalar_tac) (by scalar_tac)
  by_cases an : a.val % 2147483648 > 2139095040
  · simp_all [WP.spec_ok]
  · simp only [an, ↓reduceIte]
    by_cases bn : b.val % 2147483648 > 2139095040
    · simp_all [WP.spec_ok]
    · simp only [bn, ↓reduceIte]
      step with compare_float_raw32 0#u16 (UScalar.cast .U64 a) (UScalar.cast .U64 b) (by scalar_tac) (by scalar_tac) (by decide) as ⟨eq, heq⟩
      simp only [U32.cast_U64_val_eq, rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at heq
      rw [heq]
      by_cases eqtrue : rawEqual 2147483648 a.val b.val = true
      · simp only [eqtrue, ↓reduceIte, WP.spec_ok]
        simpa [an, bn, eqtrue, UScalar.val_or, UScalar.val_and] using pure
      · simp only [eqtrue, Bool.false_eq_true, ↓reduceIte, lift, Bind.bind, bind_ok]
        step with compare_float_raw32 2#u16 (UScalar.cast .U64 a) (UScalar.cast .U64 b) (by scalar_tac) (by scalar_tac) (by decide) as ⟨lt, hlt⟩
        simp only [U32.cast_U64_val_eq, rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at hlt
        rw [hlt]
        cases hl : rawLess 2147483648 a.val b.val <;> simpa [an, bn, eqtrue, hl] using pure

@[step] theorem binary32_max_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U32) :
    runtime.interp.float.binary32 ops 5#u16 a b ⦃ result => floatOfBits 32 result.val ∈ fmax_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  have mask (x : U32) : (x &&& 2147483647#u32).val = x.val % 2147483648 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 31
  unfold runtime.interp.float.binary32
  with_unfolding_all change (lift (a &&& 2147483647#u32) >>= fun am =>
    if am > 2139095040#u32 then Result.ok 2143289344#u32 else
    lift (b &&& 2147483647#u32) >>= fun bm =>
    if bm > 2139095040#u32 then Result.ok 2143289344#u32 else
    lift (UScalar.cast .U64 a) >>= fun av => lift (UScalar.cast .U64 b) >>= fun bv =>
    runtime.interp.float.compare_float 0#u16 av bv 32#u32 >>= fun eq =>
    if eq then (if 5#u16 = 4#u16 then Result.ok (a ||| b) else Result.ok (a &&& b)) else
    lift (UScalar.cast .U64 a) >>= fun av => lift (UScalar.cast .U64 b) >>= fun bv =>
    runtime.interp.float.compare_float 2#u16 av bv 32#u32 >>= fun lt =>
    if lt = (5#u16 = 4#u16) then Result.ok a else Result.ok b) ⦃ result => floatOfBits 32 result.val ∈ fmax_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  simp [lift, Bind.bind, bind_ok, UScalar.lt_equiv, mask]
  have pure := raw_max32_sound a.val b.val (by scalar_tac) (by scalar_tac)
  by_cases an : a.val % 2147483648 > 2139095040
  · simp_all [WP.spec_ok]
  · simp only [an, ↓reduceIte]
    by_cases bn : b.val % 2147483648 > 2139095040
    · simp_all [WP.spec_ok]
    · simp only [bn, ↓reduceIte]
      step with compare_float_raw32 0#u16 (UScalar.cast .U64 a) (UScalar.cast .U64 b) (by scalar_tac) (by scalar_tac) (by decide) as ⟨eq, heq⟩
      simp only [U32.cast_U64_val_eq, rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at heq
      rw [heq]
      by_cases eqtrue : rawEqual 2147483648 a.val b.val = true
      · simp only [eqtrue, ↓reduceIte, WP.spec_ok]
        simpa [an, bn, eqtrue, UScalar.val_or, UScalar.val_and] using pure
      · simp only [eqtrue, Bool.false_eq_true, ↓reduceIte, lift, Bind.bind, bind_ok]
        step with compare_float_raw32 2#u16 (UScalar.cast .U64 a) (UScalar.cast .U64 b) (by scalar_tac) (by scalar_tac) (by decide) as ⟨lt, hlt⟩
        simp only [U32.cast_U64_val_eq, rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at hlt
        rw [hlt]
        cases hl : rawLess 2147483648 a.val b.val <;> simpa [an, bn, eqtrue, hl] using pure

@[step] theorem binary64_min_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.binary64 ops 4#u16 a b ⦃ result => floatOfBits 64 result.val ∈ fmin_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  have mask (x : U64) : (x &&& 9223372036854775807#u64).val = x.val % 9223372036854775808 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 63
  unfold runtime.interp.float.binary64
  with_unfolding_all change (lift (a &&& 9223372036854775807#u64) >>= fun am =>
    if am > 9218868437227405312#u64 then Result.ok 9221120237041090560#u64 else
    lift (b &&& 9223372036854775807#u64) >>= fun bm =>
    if bm > 9218868437227405312#u64 then Result.ok 9221120237041090560#u64 else

    runtime.interp.float.compare_float 0#u16 a b 64#u32 >>= fun eq =>
    if eq then (if 4#u16 = 4#u16 then Result.ok (a ||| b) else Result.ok (a &&& b)) else

    runtime.interp.float.compare_float 2#u16 a b 64#u32 >>= fun lt =>
    if lt = (4#u16 = 4#u16) then Result.ok a else Result.ok b) ⦃ result => floatOfBits 64 result.val ∈ fmin_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  simp [lift, Bind.bind, bind_ok, UScalar.lt_equiv, mask]
  have pure := raw_min64_sound a.val b.val (by scalar_tac) (by scalar_tac)
  by_cases an : a.val % 9223372036854775808 > 9218868437227405312
  · simp_all [WP.spec_ok]
  · simp only [an, ↓reduceIte]
    by_cases bn : b.val % 9223372036854775808 > 9218868437227405312
    · simp_all [WP.spec_ok]
    · simp only [bn, ↓reduceIte]
      step with compare_float_raw64 0#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨eq, heq⟩
      simp only [rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at heq
      rw [heq]
      by_cases eqtrue : rawEqual 9223372036854775808 a.val b.val = true
      · simp only [eqtrue, ↓reduceIte, WP.spec_ok]
        simpa [an, bn, eqtrue, UScalar.val_or, UScalar.val_and] using pure
      · simp only [eqtrue, Bool.false_eq_true, ↓reduceIte, lift, Bind.bind, bind_ok]
        step with compare_float_raw64 2#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨lt, hlt⟩
        simp only [rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at hlt
        rw [hlt]
        cases hl : rawLess 9223372036854775808 a.val b.val <;> simpa [an, bn, eqtrue, hl] using pure

@[step] theorem binary64_max_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.binary64 ops 5#u16 a b ⦃ result => floatOfBits 64 result.val ∈ fmax_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  have mask (x : U64) : (x &&& 9223372036854775807#u64).val = x.val % 9223372036854775808 := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 63
  unfold runtime.interp.float.binary64
  with_unfolding_all change (lift (a &&& 9223372036854775807#u64) >>= fun am =>
    if am > 9218868437227405312#u64 then Result.ok 9221120237041090560#u64 else
    lift (b &&& 9223372036854775807#u64) >>= fun bm =>
    if bm > 9218868437227405312#u64 then Result.ok 9221120237041090560#u64 else

    runtime.interp.float.compare_float 0#u16 a b 64#u32 >>= fun eq =>
    if eq then (if 5#u16 = 4#u16 then Result.ok (a ||| b) else Result.ok (a &&& b)) else

    runtime.interp.float.compare_float 2#u16 a b 64#u32 >>= fun lt =>
    if lt = (5#u16 = 4#u16) then Result.ok a else Result.ok b) ⦃ result => floatOfBits 64 result.val ∈ fmax_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  simp [lift, Bind.bind, bind_ok, UScalar.lt_equiv, mask]
  have pure := raw_max64_sound a.val b.val (by scalar_tac) (by scalar_tac)
  by_cases an : a.val % 9223372036854775808 > 9218868437227405312
  · simp_all [WP.spec_ok]
  · simp only [an, ↓reduceIte]
    by_cases bn : b.val % 9223372036854775808 > 9218868437227405312
    · simp_all [WP.spec_ok]
    · simp only [bn, ↓reduceIte]
      step with compare_float_raw64 0#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨eq, heq⟩
      simp only [rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at heq
      rw [heq]
      by_cases eqtrue : rawEqual 9223372036854775808 a.val b.val = true
      · simp only [eqtrue, ↓reduceIte, WP.spec_ok]
        simpa [an, bn, eqtrue, UScalar.val_or, UScalar.val_and] using pure
      · simp only [eqtrue, Bool.false_eq_true, ↓reduceIte, lift, Bind.bind, bind_ok]
        step with compare_float_raw64 2#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨lt, hlt⟩
        simp only [rawCompare, an, bn, ↓reduceIte, Bool.false_eq_true, or_self] at hlt
        rw [hlt]
        cases hl : rawLess 9223372036854775808 a.val b.val <;> simpa [an, bn, eqtrue, hl] using pure

@[step] theorem scalar_f32_min {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 150#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fmin_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (150#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fmin_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_min_sound ops (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_max {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 151#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fmax_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (151#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fmax_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_max_sound ops (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f64_min {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 164#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fmin_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (164#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fmin_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  step with binary64_min_sound ops a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_max {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 165#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fmax_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (165#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fmax_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  step with binary64_max_sound ops a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

end Itasca.Interp

end

/-! ## FloatSigns -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly.Builtins WebAssembly.Builtins.Float Platform

@[step] theorem scalar_f32_abs {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 139#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fabs_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (139#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fabs_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with unary32_abs_sound ops (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_neg {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 140#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fneg_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (140#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fneg_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with unary32_neg_sound ops (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_copysign {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 152#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fcopysign_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (152#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fcopysign_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with binary32_copysign_sound ops (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f64_abs {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 153#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fabs_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (153#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fabs_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  step with unary64_abs_sound ops a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_neg {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 154#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fneg_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (154#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fneg_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  step with unary64_neg_sound ops a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_copysign {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 166#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fcopysign_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (166#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fcopysign_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  step with binary64_copysign_sound ops a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

end Itasca.Interp

end

/-! ## FloatBounded -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly.Builtins WebAssembly.Builtins.Float Platform
@[step] theorem scalar_f32_convert_i32_s_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 178#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I32 a) >>= fun arg => ops.f32_convert_i32_s arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonical_closed_convert 32 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_convert_i32_u_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 179#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .U (.mk_uN (UScalar.cast .U32 a).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.cast .U32 a) >>= fun arg => ops.f32_convert_i32_u arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .U (.mk_uN (UScalar.cast .U32 a).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i32_u (UScalar.cast .U32 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonical_closed_convert 32 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_convert_i64_s_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 180#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I64 a) >>= fun arg => ops.f32_convert_i64_s arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i64_s (UScalar.hcast .I64 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonical_closed_convert 64 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_convert_i64_u_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 181#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .U (.mk_uN a.val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (ops.f32_convert_i64_u a >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .U (.mk_uN a.val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i64_u a as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonical_closed_convert 64 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_demote_f64_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 182#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ demote__ 64 32 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (ops.f32_demote_f64 a >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ demote__ 64 32 (floatOfBits 64 a.val) ⦄
  simp only [lift, bind_ok]
  step with hf.f32_demote_f64 a as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonical_closed_demote 64 32 (by omega) _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_ceil_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 141#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fceil_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (141#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fceil_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_ceil_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_floor_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 142#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ ffloor_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (142#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ ffloor_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_floor_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_trunc_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 143#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ ftrunc_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (143#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ ftrunc_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_trunc_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_nearest_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 144#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fnearest_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (144#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fnearest_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_nearest_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_sqrt_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 145#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fsqrt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (145#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fsqrt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_sqrt_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_add_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 146#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fadd_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (146#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fadd_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_add_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_sub_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 147#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fsub_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (147#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fsub_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_sub_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_mul_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 148#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fmul_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (148#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fmul_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_mul_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_div_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 149#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fdiv_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (149#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fdiv_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_div_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_abs_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 139#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fabs_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (139#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fabs_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with unary32_abs_sound ops (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_neg_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 140#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fneg_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (140#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fneg_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with unary32_neg_sound ops (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_copysign_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 152#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fcopysign_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (152#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fcopysign_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with binary32_copysign_sound ops (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_min_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 150#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fmin_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (150#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fmin_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_min_sound ops (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_max_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 151#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fmax_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (151#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ fmax_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_max_sound ops (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · scalar_tac
  · simpa only [U32.cast_U64_val_eq] using hvalue

end Itasca.Interp

end

/-! ## FloatPromote -/

section

/-!
Floating-point promotion through its extracted bit loop. The loop relation supplies the complete f32-to-f64 promotion operation.
-/

/-! ## Float Promote Loop -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

@[step] theorem promote_loop_effect (fraction : U32)
    (positive : 0 < fraction.val) (small : fraction.val < 8388608) :
    runtime.interp.float.promote_loop fraction 897#u64 ⦃ result =>
      ∃ shifts : Nat, shifts ≤ 24 ∧ result.1.val = fraction.val * 2^shifts ∧
        result.2.val = 897 - shifts ∧ 8388608 ≤ result.1.val ∧ result.1.val < 16777216 ⦄ := by
  unfold runtime.interp.float.promote_loop
  apply loop.spec_decr_nat (fun p => 8388608 - p.1.val)
    (fun p => ∃ shifts : Nat, shifts ≤ 24 ∧ p.1.val = fraction.val * 2^shifts ∧
      p.2.val = 897 - shifts ∧ 0 < p.1.val ∧ p.1.val < 16777216)
  · rintro ⟨current, exponent⟩ ⟨shifts, count, fractionEq, exponentEq, currentPositive, currentBound⟩
    dsimp only at *
    unfold runtime.interp.float.promote_loop.body
    split
    · have nextBound : current.val < 8388608 := by scalar_tac
      have room : shifts < 24 := by
        by_contra h
        have equal : shifts = 24 := by omega
        rw [equal] at fractionEq
        norm_num at fractionEq
        omega
      step as ⟨doubled, doubleEq, doubleBits⟩
      have double : doubled.val = current.val * 2 := by
        rw [doubleEq]
        simp only [Nat.shiftLeft_eq, Nat.reducePow]
        norm_num only [U32.size, U32.numBits, UScalarTy.U32_numBits_eq, Nat.reducePow]
        omega
      step as ⟨next, nextEq⟩
      refine ⟨⟨shifts+1, by omega, ?_, ?_, by omega, by omega⟩, by omega⟩
      · rw [double, fractionEq, pow_succ]
        ring
      · omega
    · have finished : 8388608 ≤ current.val := by scalar_tac
      exact ⟨shifts, count, fractionEq, exponentEq, finished, currentBound⟩
  · dsimp only
    exact ⟨0, by omega, by simp, rfl, positive, by omega⟩

end Itasca.Interp

end

/-! ## Float Promote -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly.Builtins WebAssembly.Builtins.Float

@[step] theorem promote_sound (bits : U32) : runtime.interp.float.promote bits ⦃ result =>
    floatOfBits 64 result.val ∈ promote__ 32 64 (floatOfBits 32 bits.val) ⦄ := by
  let negative := decide (2147483648 ≤ bits.val)
  let exponent := bits.val / 8388608 % 256
  let fraction := bits.val % 8388608
  have exponentBound : exponent < 256 := Nat.mod_lt _ (by decide)
  have fractionBound : fraction < 8388608 := Nat.mod_lt _ (by decide)
  have reconstructed : bits.val = (if negative then 2147483648 else 0) + (exponent * 8388608 + fraction) := by
    have bound : bits.val < 4294967296 := by scalar_tac
    dsimp [negative, exponent, fraction]
    split <;> simp_all <;> omega
  have fractionMask : (bits &&& 8388607#u32).val = fraction := by
    rw [UScalar.val_and]
    exact Nat.and_two_pow_sub_one_eq_mod bits.val 23
  have signMask : (bits &&& 2147483648#u32).val = if negative then 2147483648 else 0 := by
    have h := congrArg UScalar.val (float_sign_mask_32 (UScalar.cast .U64 bits) (by scalar_tac))
    by_cases neg : 2147483648 ≤ bits.val <;>
      simpa [UScalar.val_and, U32.cast_U64_val_eq, negative, neg] using h
  unfold runtime.interp.float.promote
  simp only [lift, bind_ok]
  step as ⟨sign, signEq, signBits⟩
  have signValue : sign.val = if negative then 9223372036854775808 else 0 := by
    rw [signEq, U32.cast_U64_val_eq, signMask]
    cases negative <;> norm_num [Nat.shiftLeft_eq, U64.size, U64.numBits]
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  have exponentMask : (shifted &&& 255#u32).val = exponent := by
    rw [UScalar.val_and]
    change (shifted.val &&& (2^8-1)) = exponent
    rw [Nat.and_two_pow_sub_one_eq_mod, shiftedEq, Nat.shiftRight_eq_div_pow]
  split
  · have maxExponent : exponent = 255 := by scalar_tac
    split
    · have zeroFraction : fraction = 0 := by scalar_tac
      have input : bits.val = (if negative then 2147483648 else 0) + 2139095040 := by rw [reconstructed, maxExponent, zeroFraction]
      have output : (sign ||| 9218868437227405312#u64).val = (if negative then 9223372036854775808 else 0) + 9218868437227405312 := by
        rw [UScalar.val_or, signValue]
        cases negative <;> decide +kernel
      simp only [WP.spec_ok]
      simpa only [input, output] using promotion_infinity_mem negative
    · have positive : 0 < fraction := by scalar_tac
      have input : bits.val = (if negative then 2147483648 else 0) + (255 * 8388608 + fraction) := by rw [reconstructed, maxExponent]
      simp only [WP.spec_ok]
      simpa [input] using promotion_nan_mem negative fraction positive fractionBound
  · have finiteExponent : exponent < 255 := by scalar_tac
    split
    · have positiveExponent : 0 < exponent := by scalar_tac
      step as ⟨expanded, expandedEq⟩
      step as ⟨exponentWord, exponentWordEq, exponentWordBits⟩
      step as ⟨fractionWord, fractionWordEq, fractionWordBits⟩
      have expWord : exponentWord.val = (exponent + 896) * 4503599627370496 := by
        rw [exponentWordEq, U32.cast_U64_val_eq, expandedEq, exponentMask]
        norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
        omega
      have fracWord : fractionWord.val = fraction * 536870912 := by
        rw [fractionWordEq, U32.cast_U64_val_eq, fractionMask]
        norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
        omega
      rw [UScalar.val_or, UScalar.val_or, signValue, expWord, fracWord,
        packed_float64 negative (exponent+896) (fraction*536870912) (by omega) (by omega), reconstructed]
      exact promotion_normal_mem negative exponent fraction ⟨positiveExponent, finiteExponent⟩ fractionBound
    · have zeroExponent : exponent = 0 := by scalar_tac
      split
      · have zeroFraction : fraction = 0 := by scalar_tac
        have input : bits.val = if negative then 2147483648 else 0 := by rw [reconstructed, zeroExponent, zeroFraction]; simp
        simp only [WP.spec_ok]
        simpa only [input, signValue] using promotion_zero_mem negative
      · have positive : 0 < fraction := by scalar_tac
        step with promote_loop_effect (bits &&& 8388607#u32) (by omega) (by omega) as ⟨normalized, normalizedExponent, shifts, count, fractionEq, exponentEq, lower, upper⟩
        step as ⟨exponentWord, exponentWordEq, exponentWordBits⟩
        step as ⟨fractionWord, fractionWordEq, fractionWordBits⟩
        have expWord : exponentWord.val = (897 - shifts) * 4503599627370496 := by
          rw [exponentWordEq, exponentEq]
          norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
          omega
        have fracWord : fractionWord.val = (fraction * 2^shifts - 8388608) * 536870912 := by
          have mask : (normalized &&& 8388607#u32).val = normalized.val % 8388608 := by
            rw [UScalar.val_and]
            exact Nat.and_two_pow_sub_one_eq_mod normalized.val 23
          rw [fractionWordEq, U32.cast_U64_val_eq, mask]
          norm_num only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.U64_numBits_eq, Nat.reducePow]
          rw [fractionMask] at fractionEq
          omega
        have normalizedBounds : 8388608 ≤ fraction * 2^shifts ∧ fraction * 2^shifts < 16777216 := by
          rw [fractionMask] at fractionEq
          omega
        rw [UScalar.val_or, UScalar.val_or, signValue, expWord, fracWord,
          packed_float64 negative (897-shifts) ((fraction*2^shifts-8388608)*536870912) (by omega) (by omega), reconstructed]
        simp only [zeroExponent, Nat.zero_mul, Nat.zero_add]
        exact promotion_subnormal_mem negative fraction shifts positive fractionBound count normalizedBounds

@[step] theorem scalar_f64_promote_f32 {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 187#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈
        promote__ 32 64 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.cast .U32 a) >>= fun bits =>
    runtime.interp.float.promote bits >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ promote__ 32 64 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  simp only [lift]
  step with promote_sound (UScalar.cast .U32 a) as ⟨value, chosen⟩
  exact ⟨value, rfl, chosen⟩

end Itasca.Interp

end

end

end

/-! ## SourceRelations -/

section

/-!
# Source Relations

Floating-point reinterpretation and comparison relations connect source values to machine words.
-/

/-! ## FloatComparisonScalar -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly.Builtins WebAssembly.Builtins.Float

@[step] theorem scalar_f32_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 91#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (91#u16 - 91#u16 >>= fun index =>
    lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U64 av) >>= fun ax =>
    lift (UScalar.cast .U32 b) >>= fun bv => lift (UScalar.cast .U64 bv) >>= fun bx =>
    runtime.interp.float.compare_float index ax bx 32#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw32 0#u16 (UScalar.cast .U64 (UScalar.cast .U32 a)) (UScalar.cast .U64 (UScalar.cast .U32 b)) (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  simp only [U32.cast_U64_val_eq] at effect
  rw [effect]
  rw [raw_compare_eq32 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [feq_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f32_ne {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 92#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (92#u16 - 91#u16 >>= fun index =>
    lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U64 av) >>= fun ax =>
    lift (UScalar.cast .U32 b) >>= fun bv => lift (UScalar.cast .U64 bv) >>= fun bx =>
    runtime.interp.float.compare_float index ax bx 32#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw32 1#u16 (UScalar.cast .U64 (UScalar.cast .U32 a)) (UScalar.cast .U64 (UScalar.cast .U32 b)) (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  simp only [U32.cast_U64_val_eq] at effect
  rw [effect]
  rw [raw_compare_ne32 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fne_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f32_lt {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 93#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (93#u16 - 91#u16 >>= fun index =>
    lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U64 av) >>= fun ax =>
    lift (UScalar.cast .U32 b) >>= fun bv => lift (UScalar.cast .U64 bv) >>= fun bx =>
    runtime.interp.float.compare_float index ax bx 32#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw32 2#u16 (UScalar.cast .U64 (UScalar.cast .U32 a)) (UScalar.cast .U64 (UScalar.cast .U32 b)) (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  simp only [U32.cast_U64_val_eq] at effect
  rw [effect]
  rw [raw_compare_lt32 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [flt_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f32_gt {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 94#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (94#u16 - 91#u16 >>= fun index =>
    lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U64 av) >>= fun ax =>
    lift (UScalar.cast .U32 b) >>= fun bv => lift (UScalar.cast .U64 bv) >>= fun bx =>
    runtime.interp.float.compare_float index ax bx 32#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw32 3#u16 (UScalar.cast .U64 (UScalar.cast .U32 a)) (UScalar.cast .U64 (UScalar.cast .U32 b)) (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  simp only [U32.cast_U64_val_eq] at effect
  rw [effect]
  rw [raw_compare_gt32 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fgt_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f32_le {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 95#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (95#u16 - 91#u16 >>= fun index =>
    lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U64 av) >>= fun ax =>
    lift (UScalar.cast .U32 b) >>= fun bv => lift (UScalar.cast .U64 bv) >>= fun bx =>
    runtime.interp.float.compare_float index ax bx 32#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw32 4#u16 (UScalar.cast .U64 (UScalar.cast .U32 a)) (UScalar.cast .U64 (UScalar.cast .U32 b)) (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  simp only [U32.cast_U64_val_eq] at effect
  rw [effect]
  rw [raw_compare_le32 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fle_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f32_ge {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 96#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (96#u16 - 91#u16 >>= fun index =>
    lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U64 av) >>= fun ax =>
    lift (UScalar.cast .U32 b) >>= fun bv => lift (UScalar.cast .U64 bv) >>= fun bx =>
    runtime.interp.float.compare_float index ax bx 32#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw32 5#u16 (UScalar.cast .U64 (UScalar.cast .U32 a)) (UScalar.cast .U64 (UScalar.cast .U32 b)) (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  simp only [U32.cast_U64_val_eq] at effect
  rw [effect]
  rw [raw_compare_ge32 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fge_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f64_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 97#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (97#u16 - 97#u16 >>= fun index =>
    runtime.interp.float.compare_float index a b 64#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw64 0#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  rw [effect]
  rw [raw_compare_eq64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [feq_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f64_ne {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 98#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (98#u16 - 97#u16 >>= fun index =>
    runtime.interp.float.compare_float index a b 64#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw64 1#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  rw [effect]
  rw [raw_compare_ne64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fne_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f64_lt {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 99#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (99#u16 - 97#u16 >>= fun index =>
    runtime.interp.float.compare_float index a b 64#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw64 2#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  rw [effect]
  rw [raw_compare_lt64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [flt_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f64_gt {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 100#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (100#u16 - 97#u16 >>= fun index =>
    runtime.interp.float.compare_float index a b 64#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw64 3#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  rw [effect]
  rw [raw_compare_gt64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fgt_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f64_le {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 101#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (101#u16 - 97#u16 >>= fun index =>
    runtime.interp.float.compare_float index a b 64#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw64 4#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  rw [effect]
  rw [raw_compare_le64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fle_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

@[step] theorem scalar_f64_ge {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 102#u16 a b ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (102#u16 - 97#u16 >>= fun index =>
    runtime.interp.float.compare_float index a b 64#u32 >>= fun answer =>
    lift (UScalar.cast_fromBool .U64 answer) >>= fun value =>
    Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val = proj_uN_0 (fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  step as ⟨index, indexValue⟩
  have exactIndex : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift]
  step with compare_float_raw64 5#u16 a b (by scalar_tac) (by scalar_tac) (by decide) as ⟨answer, effect⟩
  rw [effect]
  rw [raw_compare_ge64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fge_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

end Itasca.Interp

end

/-! ## FloatSource -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float Platform

/-- Actual f32.abs dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_abs_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 139#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .ABS)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_abs ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .ABS (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_abs_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.neg dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_neg_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 140#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .NEG)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_neg ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .NEG (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_neg_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.ceil dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_ceil_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 141#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .CEIL)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ceil ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .CEIL (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_ceil_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.floor dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_floor_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 142#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .FLOOR)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_floor ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .FLOOR (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_floor_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.trunc dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_trunc_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 143#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .TRUNC)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_trunc ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .TRUNC (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_trunc_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.nearest dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_nearest_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 144#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .NEAREST)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_nearest ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .NEAREST (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_nearest_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.sqrt dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_sqrt_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 145#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .UNOP .F32 (.mk_unop__1 .F32 .SQRT)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_sqrt ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F32 .SQRT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_sqrt_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.add dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_add_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 146#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .ADD)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_add ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .ADD (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_add_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.sub dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_sub_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 147#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .SUB)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_sub ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .SUB (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_sub_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.mul dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_mul_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 148#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .MUL)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_mul ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .MUL (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_mul_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.div dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_div_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 149#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .DIV)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_div ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .DIV (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_div_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.copysign dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_copysign_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 152#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .COPYSIGN)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_copysign ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .COPYSIGN (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_copysign_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f64.abs dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_abs_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 153#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .ABS)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_abs ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .ABS (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_abs_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.neg dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_neg_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 154#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .NEG)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_neg ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .NEG (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_neg_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.ceil dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_ceil_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 155#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .CEIL)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ceil ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .CEIL (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_ceil_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.floor dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_floor_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 156#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .FLOOR)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_floor ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .FLOOR (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_floor_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.trunc dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_trunc_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 157#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .TRUNC)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_trunc ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .TRUNC (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_trunc_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.nearest dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_nearest_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 158#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .NEAREST)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_nearest ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .NEAREST (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_nearest_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.sqrt dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_sqrt_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 159#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .UNOP .F64 (.mk_unop__1 .F64 .SQRT)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_sqrt ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_unary_pure .F64 .SQRT (floatOfBits 64 a.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_sqrt_relation (floatOfBits 64 a.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.add dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_add_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 160#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .ADD)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_add ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .ADD (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_add_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.sub dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_sub_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 161#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .SUB)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_sub ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .SUB (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_sub_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.mul dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_mul_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 162#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .MUL)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_mul ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .MUL (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_mul_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.div dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_div_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops)
    (a b : U64) :
    runtime.interp.float.scalar ops 163#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .DIV)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_div ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .DIV (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_div_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.copysign dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_copysign_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 166#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .COPYSIGN)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_copysign ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .COPYSIGN (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_copysign_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

end Itasca.Interp

end

/-! ## FloatConvertSource -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float Platform

theorem scalar_f32_convert_i32_s_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 178#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)),
        .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 (.CONVERT .S))]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i32_s ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I32 .F32 .S _ (by change _ < 2 ^ 32; scalar_tac) _ chosen

theorem scalar_f32_convert_i32_u_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 179#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)),
        .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 (.CONVERT .U))]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i32_u ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I32 .F32 .U _ (by change _ < 2 ^ 32; scalar_tac) _ chosen

theorem scalar_f32_convert_i64_s_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 180#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)),
        .CVTOP .F32 .I64 (.mk_cvtop___1 .I64 .F32 (.CONVERT .S))]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i64_s ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I64 .F32 .S _ (by change _ < 2 ^ 64; scalar_tac) _ chosen

theorem scalar_f32_convert_i64_u_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 181#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN a.val)),
        .CVTOP .F32 .I64 (.mk_cvtop___1 .I64 .F32 (.CONVERT .U))]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i64_u ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I64 .F32 .U _ (by change _ < 2 ^ 64; scalar_tac) _ chosen

theorem scalar_f64_convert_i32_s_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 183#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)),
        .CVTOP .F64 .I32 (.mk_cvtop___1 .I32 .F64 (.CONVERT .S))]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_s ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I32 .F64 .S _ (by change _ < 2 ^ 32; scalar_tac) _ chosen

theorem scalar_f64_convert_i32_u_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 184#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)),
        .CVTOP .F64 .I32 (.mk_cvtop___1 .I32 .F64 (.CONVERT .U))]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_u ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I32 .F64 .U _ (by change _ < 2 ^ 32; scalar_tac) _ chosen

theorem scalar_f64_convert_i64_s_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 185#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)),
        .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 (.CONVERT .S))]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_s ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I64 .F64 .S _ (by change _ < 2 ^ 64; scalar_tac) _ chosen

theorem scalar_f64_convert_i64_u_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 186#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN a.val)),
        .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 (.CONVERT .U))]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_u ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  exact Spec.float_convert_pure .I64 .F64 .U _ (by change _ < 2 ^ 64; scalar_tac) _ chosen

theorem scalar_f32_demote_f64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 182#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CVTOP .F32 .F64 (.mk_cvtop___3 .F64 .F32 .DEMOTE)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_demote_f64 ops correct a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.numeric_conversion_pure _ _ _ _ _ _ (Spec.float_demote_relation _)
  · exact List.mem_map.mpr ⟨_, chosen, rfl⟩
  · exact Spec.float_num_wf .F64 _ (float_of_bits_wf 64 (by omega) _)
  · exact Spec.float_num_wf .F32 _ (float_of_bits_wf 32 (by omega) _)
  · exact .cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Interp

end

/-! ## FloatMinMaxSource -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

/-- Actual f32.min dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_min_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 150#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .MIN)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_min ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .MIN (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_min_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f32.max dispatch takes a permitted generated numeric step. -/
theorem scalar_f32_max_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 151#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)),
        .BINOP .F32 (.mk_binop__1 .F32 .MAX)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_max ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F32 .MAX (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits 32 value.val) _
  · exact Spec.float_f32_max_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (float_of_bits_wf 32 (by omega) _) (float_of_bits_wf 32 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _
  · exact float_of_bits_wf 32 (by omega) _

/-- Actual f64.min dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_min_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 164#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .MIN)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_min ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .MIN (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_min_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

/-- Actual f64.max dispatch takes a permitted generated numeric step. -/
theorem scalar_f64_max_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 165#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)),
        .BINOP .F64 (.mk_binop__1 .F64 .MAX)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_max ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.float_binary_pure .F64 .MAX (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits 64 value.val) _
  · exact Spec.float_f64_max_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (float_of_bits_wf 64 (by omega) _) (float_of_bits_wf 64 (by omega) _)
  · exact chosen
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _
  · exact float_of_bits_wf 64 (by omega) _

end Itasca.Interp

end

/-! ## FloatPromoteSource -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

theorem scalar_f64_promote_f32_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 187#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CVTOP .F64 .F32 (.mk_cvtop___3 .F32 .F64 .PROMOTE)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_promote_f32 ops a b)
  rintro result ⟨value, rfl, chosen⟩
  refine ⟨value, rfl, ?_⟩
  apply Spec.numeric_conversion_pure _ _ _ _ _ _ (Spec.float_promote_relation _)
  · exact List.mem_map.mpr ⟨_, chosen, rfl⟩
  · exact Spec.float_num_wf .F32 _ (float_of_bits_wf 32 (by omega) _)
  · exact Spec.float_num_wf .F64 _ (float_of_bits_wf 64 (by omega) _)
  · exact .cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_0 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Interp

end

/-! ## FloatReinterpretSource -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly WebAssembly.Builtins WebAssembly.Builtins.Float

theorem scalar_f64_reinterpret_i64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 191#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN a.val)), .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 191#u16 a b = .ok (.Ok (a)) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all rfl
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  exact Spec.f64_reinterpret_i64_pure _ (by scalar_tac)

theorem scalar_i64_reinterpret_f64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 189#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)), .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET)]
        [.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 189#u16 a b = .ok (.Ok (a)) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all rfl
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  exact Spec.i64_reinterpret_f64_pure _ (by scalar_tac)

end Itasca.Interp

end

end
