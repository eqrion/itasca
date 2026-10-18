import Exec.Interp.Numeric.Float.FloatCompare
import SpecExt.Builtins.Float.MinMax

set_option maxHeartbeats 1000000
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

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

end Exec.Interp
