import Exec.Generated.Funs
import Exec.Platform.Float
import Exec.Spec.Float
import SpecExt.Builtins.Float.Sign

/-! Refinement of the extracted NaN-canonicalizing wrappers. These lemmas use
ordinary integer/bitvector semantics and the checked IEEE decoder. -/

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform

@[step] theorem quiet32_bits (bits : U32) :
    runtime.interp.float.quiet32 bits ⦃ result =>
      result = if bits.val % 2147483648 > 2139095040 then 2143289344#u32 else bits ⦄ := by
  have hm : (bits &&& 2147483647#u32).val = bits.val % 2147483648 := by
    rw [UScalar.val_and]
    change (bits.val &&& (2 ^ 31 - 1)) = bits.val % (2 ^ 31)
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  unfold runtime.interp.float.quiet32
  rw [lift, bind_ok]
  by_cases hn : bits.val % 2147483648 > 2139095040
  · have h : (bits &&& 2147483647#u32) > 2139095040#u32 := by
      simpa [UScalar.lt_equiv, hm] using hn
    rw [if_pos h]
    simp [WP.spec_ok, hn]
  · have h : ¬ (bits &&& 2147483647#u32) > 2139095040#u32 := by
      simpa [UScalar.lt_equiv, hm] using hn
    rw [if_neg h]
    simp [WP.spec_ok, hn]

@[step] theorem quiet32_decode (bits : U32) :
    runtime.interp.float.quiet32 bits ⦃ result =>
      floatOfBits 32 result.val =
        if isNaN (floatOfBits 32 bits.val) then fN.POS (.NAN (canon_ 32)) else floatOfBits 32 bits.val ⦄ := by
  obtain ⟨result, hr, heq⟩ := WP.spec_imp_exists (quiet32_bits bits)
  rw [hr]
  simp only [WP.spec_ok]
  rw [heq, isNaN_floatOfBits_32]
  by_cases hn : bits.val % 2147483648 > 2139095040
  · simp only [hn, if_true, decide_true]
    decide +kernel
  · simp [hn]

/-- Canonicalization turns A1's raw float outcome into a permitted spec result. -/
theorem quiet32_sound (bits : U32) (allowed : List fN)
    (h : FloatOutcome (floatOfBits 32 bits.val) allowed)
    (hc : CanonicalClosed 32 allowed) :
    runtime.interp.float.quiet32 bits ⦃ result => floatOfBits 32 result.val ∈ allowed ⦄ := by
  obtain ⟨result, hr, heq⟩ := WP.spec_imp_exists (quiet32_decode bits)
  rw [hr]
  simp only [WP.spec_ok]
  rw [heq]
  exact floatOutcome_canonicalize 32 (floatOfBits 32 bits.val) allowed h hc

@[step] theorem quiet64_bits (bits : U64) :
    runtime.interp.float.quiet64 bits ⦃ result =>
      result = if bits.val % 9223372036854775808 > 9218868437227405312 then 9221120237041090560#u64 else bits ⦄ := by
  have hm : (bits &&& 9223372036854775807#u64).val = bits.val % 9223372036854775808 := by
    rw [UScalar.val_and]
    change (bits.val &&& (2 ^ 63 - 1)) = bits.val % (2 ^ 63)
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  unfold runtime.interp.float.quiet64
  rw [lift, bind_ok]
  by_cases hn : bits.val % 9223372036854775808 > 9218868437227405312
  · have h : (bits &&& 9223372036854775807#u64) > 9218868437227405312#u64 := by
      simpa [UScalar.lt_equiv, hm] using hn
    rw [if_pos h]
    simp [WP.spec_ok, hn]
  · have h : ¬ (bits &&& 9223372036854775807#u64) > 9218868437227405312#u64 := by
      simpa [UScalar.lt_equiv, hm] using hn
    rw [if_neg h]
    simp [WP.spec_ok, hn]

@[step] theorem quiet64_decode (bits : U64) :
    runtime.interp.float.quiet64 bits ⦃ result =>
      floatOfBits 64 result.val =
        if isNaN (floatOfBits 64 bits.val) then fN.POS (.NAN (canon_ 64)) else floatOfBits 64 bits.val ⦄ := by
  obtain ⟨result, hr, heq⟩ := WP.spec_imp_exists (quiet64_bits bits)
  rw [hr]
  simp only [WP.spec_ok]
  rw [heq, isNaN_floatOfBits_64]
  by_cases hn : bits.val % 9223372036854775808 > 9218868437227405312
  · simp only [hn, if_true, decide_true]
    decide +kernel
  · simp [hn]

/-- Canonicalization turns A1's raw float outcome into a permitted spec result. -/
theorem quiet64_sound (bits : U64) (allowed : List fN)
    (h : FloatOutcome (floatOfBits 64 bits.val) allowed)
    (hc : CanonicalClosed 64 allowed) :
    runtime.interp.float.quiet64 bits ⦃ result => floatOfBits 64 result.val ∈ allowed ⦄ := by
  obtain ⟨result, hr, heq⟩ := WP.spec_imp_exists (quiet64_decode bits)
  rw [hr]
  simp only [WP.spec_ok]
  rw [heq]
  exact floatOutcome_canonicalize 64 (floatOfBits 64 bits.val) allowed h hc

@[step] theorem binary32_add_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 0#u16 a b ⦃ result =>
      floatOfBits 32 result.val ∈ fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_add a b >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  step with hf.f32_add a b as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_add 32 (by omega) _ _)

@[step] theorem binary32_sub_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 1#u16 a b ⦃ result =>
      floatOfBits 32 result.val ∈ fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_sub a b >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  step with hf.f32_sub a b as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_sub 32 (by omega) _ _)

@[step] theorem binary32_mul_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 2#u16 a b ⦃ result =>
      floatOfBits 32 result.val ∈ fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_mul a b >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  step with hf.f32_mul a b as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_mul 32 (by omega) _ _)

@[step] theorem binary32_div_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 3#u16 a b ⦃ result =>
      floatOfBits 32 result.val ∈ fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_div a b >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  step with hf.f32_div a b as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_div 32 (by omega) _ _)

@[step] theorem unary32_ceil_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 2#u16 a ⦃ result =>
      floatOfBits 32 result.val ∈ fceil_ 32 (floatOfBits 32 a.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_ceil a >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fceil_ 32 (floatOfBits 32 a.val) ⦄
  step with hf.f32_ceil a as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_integral 32 (by omega) _ _)

@[step] theorem unary32_floor_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 3#u16 a ⦃ result =>
      floatOfBits 32 result.val ∈ ffloor_ 32 (floatOfBits 32 a.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_floor a >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ ffloor_ 32 (floatOfBits 32 a.val) ⦄
  step with hf.f32_floor a as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_integral 32 (by omega) _ _)

@[step] theorem unary32_trunc_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 4#u16 a ⦃ result =>
      floatOfBits 32 result.val ∈ ftrunc_ 32 (floatOfBits 32 a.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_trunc a >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ ftrunc_ 32 (floatOfBits 32 a.val) ⦄
  step with hf.f32_trunc a as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_integral 32 (by omega) _ _)

@[step] theorem unary32_nearest_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 5#u16 a ⦃ result =>
      floatOfBits 32 result.val ∈ fnearest_ 32 (floatOfBits 32 a.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_nearest a >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fnearest_ 32 (floatOfBits 32 a.val) ⦄
  step with hf.f32_nearest a as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_integral 32 (by omega) _ _)

@[step] theorem unary32_sqrt_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 6#u16 a ⦃ result =>
      floatOfBits 32 result.val ∈ fsqrt_ 32 (floatOfBits 32 a.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_sqrt a >>= runtime.interp.float.quiet32) ⦃ result => floatOfBits 32 result.val ∈ fsqrt_ 32 (floatOfBits 32 a.val) ⦄
  step with hf.f32_sqrt a as ⟨raw, hraw⟩
  exact quiet32_sound raw _ hraw (canonicalClosed_sqrt 32 (by omega) _)

@[step] theorem binary64_add_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 0#u16 a b ⦃ result =>
      floatOfBits 64 result.val ∈ fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_add a b >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step with hf.f64_add a b as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_add 64 (by omega) _ _)

@[step] theorem binary64_sub_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 1#u16 a b ⦃ result =>
      floatOfBits 64 result.val ∈ fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_sub a b >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step with hf.f64_sub a b as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_sub 64 (by omega) _ _)

@[step] theorem binary64_mul_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 2#u16 a b ⦃ result =>
      floatOfBits 64 result.val ∈ fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_mul a b >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step with hf.f64_mul a b as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_mul 64 (by omega) _ _)

@[step] theorem binary64_div_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 3#u16 a b ⦃ result =>
      floatOfBits 64 result.val ∈ fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_div a b >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step with hf.f64_div a b as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_div 64 (by omega) _ _)

@[step] theorem unary64_ceil_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 2#u16 a ⦃ result =>
      floatOfBits 64 result.val ∈ fceil_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_ceil a >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fceil_ 64 (floatOfBits 64 a.val) ⦄
  step with hf.f64_ceil a as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_integral 64 (by omega) _ _)

@[step] theorem unary64_floor_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 3#u16 a ⦃ result =>
      floatOfBits 64 result.val ∈ ffloor_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_floor a >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ ffloor_ 64 (floatOfBits 64 a.val) ⦄
  step with hf.f64_floor a as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_integral 64 (by omega) _ _)

@[step] theorem unary64_trunc_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 4#u16 a ⦃ result =>
      floatOfBits 64 result.val ∈ ftrunc_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_trunc a >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ ftrunc_ 64 (floatOfBits 64 a.val) ⦄
  step with hf.f64_trunc a as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_integral 64 (by omega) _ _)

@[step] theorem unary64_nearest_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 5#u16 a ⦃ result =>
      floatOfBits 64 result.val ∈ fnearest_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_nearest a >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fnearest_ 64 (floatOfBits 64 a.val) ⦄
  step with hf.f64_nearest a as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_integral 64 (by omega) _ _)

@[step] theorem unary64_sqrt_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 6#u16 a ⦃ result =>
      floatOfBits 64 result.val ∈ fsqrt_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_sqrt a >>= runtime.interp.float.quiet64) ⦃ result => floatOfBits 64 result.val ∈ fsqrt_ 64 (floatOfBits 64 a.val) ⦄
  step with hf.f64_sqrt a as ⟨raw, hraw⟩
  exact quiet64_sound raw _ hraw (canonicalClosed_sqrt 64 (by omega) _)

@[step] theorem scalar_f32_convert_i32_s {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 178#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I32 a) >>= fun arg => ops.f32_convert_i32_s arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_convert_i32_u {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 179#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .U (.mk_uN (UScalar.cast .U32 a).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.cast .U32 a) >>= fun arg => ops.f32_convert_i32_u arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .U (.mk_uN (UScalar.cast .U32 a).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i32_u (UScalar.cast .U32 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_convert_i64_s {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 180#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I64 a) >>= fun arg => ops.f32_convert_i64_s arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i64_s (UScalar.hcast .I64 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 64 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_convert_i64_u {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 181#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .U (.mk_uN a.val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (ops.f32_convert_i64_u a >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ [convert__ 64 32 .U (.mk_uN a.val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i64_u a as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 64 32 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f64_convert_i32_s {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 183#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I32 a) >>= fun arg => ops.f64_convert_i32_s arg >>= fun raw => runtime.interp.float.quiet64 raw >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f64_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw, hraw⟩
  step with quiet64_sound raw _ hraw (canonicalClosed_convert 32 64 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_convert_i32_u {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 184#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 32 64 .U (.mk_uN (UScalar.cast .U32 a).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.cast .U32 a) >>= fun arg => ops.f64_convert_i32_u arg >>= fun raw => runtime.interp.float.quiet64 raw >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 32 64 .U (.mk_uN (UScalar.cast .U32 a).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f64_convert_i32_u (UScalar.cast .U32 a) as ⟨raw, hraw⟩
  step with quiet64_sound raw _ hraw (canonicalClosed_convert 32 64 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_convert_i64_s {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 185#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I64 a) >>= fun arg => ops.f64_convert_i64_s arg >>= fun raw => runtime.interp.float.quiet64 raw >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f64_convert_i64_s (UScalar.hcast .I64 a) as ⟨raw, hraw⟩
  step with quiet64_sound raw _ hraw (canonicalClosed_convert 64 64 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_convert_i64_u {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 186#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 64 64 .U (.mk_uN a.val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (ops.f64_convert_i64_u a >>= fun raw => runtime.interp.float.quiet64 raw >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ [convert__ 64 64 .U (.mk_uN a.val)] ⦄
  step with hf.f64_convert_i64_u a as ⟨raw, hraw⟩
  step with quiet64_sound raw _ hraw (canonicalClosed_convert 64 64 (by omega) _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f32_demote_f64 {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 182#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ demote__ 64 32 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (ops.f32_demote_f64 a >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ demote__ 64 32 (floatOfBits 64 a.val) ⦄
  simp only [lift, bind_ok]
  step with hf.f32_demote_f64 a as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonicalClosed_demote 64 32 (by omega) _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_ceil {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 141#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fceil_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (141#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fceil_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_ceil_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_floor {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 142#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ ffloor_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (142#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ ffloor_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_floor_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_trunc {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 143#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ ftrunc_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (143#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ ftrunc_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_trunc_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_nearest {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 144#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fnearest_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (144#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fnearest_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_nearest_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_sqrt {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 145#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fsqrt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (145#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fsqrt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_sqrt_sound ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_add {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 146#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fadd_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (146#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fadd_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_add_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_sub {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 147#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fsub_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (147#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fsub_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_sub_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_mul {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 148#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fmul_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (148#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fmul_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_mul_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f32_div {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 149#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fdiv_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (149#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 32 value.val ∈ fdiv_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_div_sound ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

@[step] theorem scalar_f64_ceil {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 155#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fceil_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (155#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fceil_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  step with unary64_ceil_sound ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_floor {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 156#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ ffloor_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (156#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ ffloor_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  step with unary64_floor_sound ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_trunc {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 157#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ ftrunc_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (157#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ ftrunc_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  step with unary64_trunc_sound ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_nearest {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 158#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fnearest_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (158#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fnearest_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  step with unary64_nearest_sound ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_sqrt {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 159#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fsqrt_ 64 (floatOfBits 64 a.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (159#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fsqrt_ 64 (floatOfBits 64 a.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  step with unary64_sqrt_sound ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_add {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 160#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (160#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  step with binary64_add_sound ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_sub {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 161#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (161#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  step with binary64_sub_sound ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_mul {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 162#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (162#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  step with binary64_mul_sound ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

@[step] theorem scalar_f64_div {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 163#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (163#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ floatOfBits 64 value.val ∈ fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  step with binary64_div_sound ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem binary32_add_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 0#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (.mk_num__1 .F32 (floatOfBits 32 b.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary32_add_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_add_relation (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)

theorem binary32_sub_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 1#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (.mk_num__1 .F32 (floatOfBits 32 b.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary32_sub_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_sub_relation (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)

theorem binary32_mul_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 2#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (.mk_num__1 .F32 (floatOfBits 32 b.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary32_mul_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_mul_relation (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)

theorem binary32_div_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 3#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (.mk_num__1 .F32 (floatOfBits 32 b.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary32_div_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_div_relation (floatOfBits 32 a.val) (floatOfBits 32 b.val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)

theorem unary32_ceil_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 2#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F32 (.mk_unop__1 .F32 .CEIL) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary32_ceil_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fceil_ 32 (floatOfBits 32 a.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_ceil_relation (floatOfBits 32 a.val) (floatOfBits_wf 32 (by omega) _)

theorem unary32_floor_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 3#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary32_floor_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(ffloor_ 32 (floatOfBits 32 a.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_floor_relation (floatOfBits 32 a.val) (floatOfBits_wf 32 (by omega) _)

theorem unary32_trunc_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 4#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary32_trunc_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(ftrunc_ 32 (floatOfBits 32 a.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_trunc_relation (floatOfBits 32 a.val) (floatOfBits_wf 32 (by omega) _)

theorem unary32_nearest_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 5#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary32_nearest_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fnearest_ 32 (floatOfBits 32 a.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_nearest_relation (floatOfBits 32 a.val) (floatOfBits_wf 32 (by omega) _)

theorem unary32_sqrt_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 6#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F32 (.mk_unop__1 .F32 .SQRT) (.mk_num__1 .F32 (floatOfBits 32 a.val)) (some choices) ∧
        num_.mk_num__1 .F32 (floatOfBits 32 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary32_sqrt_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fsqrt_ 32 (floatOfBits 32 a.val)).map (num_.mk_num__1 .F32), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f32_sqrt_relation (floatOfBits 32 a.val) (floatOfBits_wf 32 (by omega) _)

theorem binary64_add_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 0#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary64_add_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_add_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)

theorem binary64_sub_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 1#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary64_sub_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_sub_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)

theorem binary64_mul_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 2#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary64_mul_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_mul_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)

theorem binary64_div_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 3#u16 a b ⦃ result =>
      ∃ choices, fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (binary64_div_sound ops hf a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_div_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)

theorem unary64_ceil_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 2#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F64 (.mk_unop__1 .F64 .CEIL) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary64_ceil_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fceil_ 64 (floatOfBits 64 a.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_ceil_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)

theorem unary64_floor_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 3#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary64_floor_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(ffloor_ 64 (floatOfBits 64 a.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_floor_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)

theorem unary64_trunc_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 4#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary64_trunc_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(ftrunc_ 64 (floatOfBits 64 a.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_trunc_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)

theorem unary64_nearest_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 5#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary64_nearest_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fnearest_ 64 (floatOfBits 64 a.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_nearest_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)

theorem unary64_sqrt_spec {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 6#u16 a ⦃ result =>
      ∃ choices, fun_unop_ .F64 (.mk_unop__1 .F64 .SQRT) (.mk_num__1 .F64 (floatOfBits 64 a.val)) (some choices) ∧
        num_.mk_num__1 .F64 (floatOfBits 64 result.val) ∈ choices ⦄ := by
  obtain ⟨result, hr, hm⟩ := WP.spec_imp_exists (unary64_sqrt_sound ops hf a)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨(fsqrt_ 64 (floatOfBits 64 a.val)).map (num_.mk_num__1 .F64), ?_, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
  exact Spec.float_f64_sqrt_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)

/-- Bitwise sign operations preserve payloads and require no FloatOps law. -/
@[step] theorem unary32_abs_sound {F : Type} (ops : runtime.platform.FloatOps F) (bits : U32) :
    runtime.interp.float.unary32 ops 0#u16 bits ⦃ result =>
      floatOfBits 32 result.val ∈ fabs_ 32 (floatOfBits 32 bits.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change Result.ok (bits &&& 2147483647#u32) ⦃ result => floatOfBits 32 result.val ∈ fabs_ 32 (floatOfBits 32 bits.val) ⦄
  simp only [WP.spec_ok, fabs_, List.mem_singleton, UScalar.val_and]
  change floatOfBits 32 (bits.val &&& (2 ^ 31 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact floatOfBits_abs32 bits.val

/-- Bitwise sign operations preserve payloads and require no FloatOps law. -/
@[step] theorem unary32_neg_sound {F : Type} (ops : runtime.platform.FloatOps F) (bits : U32) :
    runtime.interp.float.unary32 ops 1#u16 bits ⦃ result =>
      floatOfBits 32 result.val ∈ fneg_ 32 (floatOfBits 32 bits.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change Result.ok (bits ^^^ 2147483648#u32) ⦃ result => floatOfBits 32 result.val ∈ fneg_ 32 (floatOfBits 32 bits.val) ⦄
  simp only [WP.spec_ok, fneg_, List.mem_singleton, UScalar.val_xor]
  exact floatOfBits_neg32 bits.val

/-- Bitwise sign operations preserve payloads and require no FloatOps law. -/
@[step] theorem unary64_abs_sound {F : Type} (ops : runtime.platform.FloatOps F) (bits : U64) :
    runtime.interp.float.unary64 ops 0#u16 bits ⦃ result =>
      floatOfBits 64 result.val ∈ fabs_ 64 (floatOfBits 64 bits.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change Result.ok (bits &&& 9223372036854775807#u64) ⦃ result => floatOfBits 64 result.val ∈ fabs_ 64 (floatOfBits 64 bits.val) ⦄
  simp only [WP.spec_ok, fabs_, List.mem_singleton, UScalar.val_and]
  change floatOfBits 64 (bits.val &&& (2 ^ 63 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact floatOfBits_abs64 bits.val

/-- Bitwise sign operations preserve payloads and require no FloatOps law. -/
@[step] theorem unary64_neg_sound {F : Type} (ops : runtime.platform.FloatOps F) (bits : U64) :
    runtime.interp.float.unary64 ops 1#u16 bits ⦃ result =>
      floatOfBits 64 result.val ∈ fneg_ 64 (floatOfBits 64 bits.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change Result.ok (bits ^^^ 9223372036854775808#u64) ⦃ result => floatOfBits 64 result.val ∈ fneg_ 64 (floatOfBits 64 bits.val) ⦄
  simp only [WP.spec_ok, fneg_, List.mem_singleton, UScalar.val_xor]
  exact floatOfBits_neg64 bits.val

@[step] theorem binary32_copysign_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U32) :
    runtime.interp.float.binary32 ops 6#u16 a b ⦃ result =>
      floatOfBits 32 result.val ∈ fcopysign_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (Aeneas.Std.bind (lift (a &&& 2147483647#u32)) (fun x => Aeneas.Std.bind (lift (b &&& 2147483648#u32)) (fun y => Result.ok (x ||| y)))) ⦃ result => floatOfBits 32 result.val ∈ fcopysign_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val) ⦄
  rw [lift, bind_ok, lift, bind_ok]
  simp only [WP.spec_ok, fcopysign_, List.mem_singleton, UScalar.val_or, UScalar.val_and]
  exact floatOfBits_copysign32 a.val b.val

@[step] theorem binary64_copysign_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.binary64 ops 6#u16 a b ⦃ result =>
      floatOfBits 64 result.val ∈ fcopysign_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (Aeneas.Std.bind (lift (a &&& 9223372036854775807#u64)) (fun x => Aeneas.Std.bind (lift (b &&& 9223372036854775808#u64)) (fun y => Result.ok (x ||| y)))) ⦃ result => floatOfBits 64 result.val ∈ fcopysign_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) ⦄
  rw [lift, bind_ok, lift, bind_ok]
  simp only [WP.spec_ok, fcopysign_, List.mem_singleton, UScalar.val_or, UScalar.val_and]
  exact floatOfBits_copysign64 a.val b.val

end Exec.Interp
