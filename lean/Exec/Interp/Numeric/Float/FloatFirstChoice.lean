import Exec.Interp.Numeric.Float.Float
import SpecExt.Builtins.Float.FirstChoice
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem quiet32_first_choice (bits : U32) (allowed : List fN)
    (outcome : FloatOutcome (floatOfBits 32 bits.val) allowed)
    (closed : CanonicalClosed 32 allowed) (family : ReplyFamily 32 allowed) :
    runtime.interp.float.quiet32 bits ⦃ result => allowed.head?=some (floatOfBits 32 result.val) ⦄ := by
  apply WP.spec_mono (quiet32_decode bits)
  intro result decoded
  rw [decoded]
  apply family.head_of_canonical_result (canonical_positive_32)
  · exact floatOutcome_canonicalize 32 _ allowed outcome closed
  · intro nan
    cases original : isNaN (floatOfBits 32 bits.val) <;> simp_all

theorem quiet64_first_choice (bits : U64) (allowed : List fN)
    (outcome : FloatOutcome (floatOfBits 64 bits.val) allowed)
    (closed : CanonicalClosed 64 allowed) (family : ReplyFamily 64 allowed) :
    runtime.interp.float.quiet64 bits ⦃ result => allowed.head?=some (floatOfBits 64 result.val) ⦄ := by
  apply WP.spec_mono (quiet64_decode bits)
  intro result decoded
  rw [decoded]
  apply family.head_of_canonical_result (canonical_positive_64)
  · exact floatOutcome_canonicalize 64 _ allowed outcome closed
  · intro nan
    cases original : isNaN (floatOfBits 64 bits.val) <;> simp_all

theorem binary32_add_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 0#u16 a b ⦃ result =>
      (fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_add a b >>= runtime.interp.float.quiet32) ⦃ result =>
    (fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_add a b as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_add 32 (by omega) _ _)
    (add_reply_family _ _ _)

theorem binary32_sub_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 1#u16 a b ⦃ result =>
      (fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_sub a b >>= runtime.interp.float.quiet32) ⦃ result =>
    (fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_sub a b as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_sub 32 (by omega) _ _)
    (sub_reply_family _ _ _)

theorem binary32_mul_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 2#u16 a b ⦃ result =>
      (fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_mul a b >>= runtime.interp.float.quiet32) ⦃ result =>
    (fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_mul a b as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_mul 32 (by omega) _ _)
    (mul_reply_family _ _ _)

theorem binary32_div_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U32) :
    runtime.interp.float.binary32 ops 3#u16 a b ⦃ result =>
      (fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.binary32
  with_unfolding_all change (ops.f32_div a b >>= runtime.interp.float.quiet32) ⦃ result =>
    (fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_div a b as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_div 32 (by omega) _ _)
    (div_reply_family _ _ _)

theorem unary32_ceil_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 2#u16 a ⦃ result =>
      (fceil_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_ceil a >>= runtime.interp.float.quiet32) ⦃ result =>
    (fceil_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_ceil a as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_integral 32 (by omega) _ _)
    (ceil_reply_family _ _)

theorem unary32_floor_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 3#u16 a ⦃ result =>
      (ffloor_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_floor a >>= runtime.interp.float.quiet32) ⦃ result =>
    (ffloor_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_floor a as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_integral 32 (by omega) _ _)
    (floor_reply_family _ _)

theorem unary32_trunc_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 4#u16 a ⦃ result =>
      (ftrunc_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_trunc a >>= runtime.interp.float.quiet32) ⦃ result =>
    (ftrunc_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_trunc a as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_integral 32 (by omega) _ _)
    (trunc_reply_family _ _)

theorem unary32_nearest_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 5#u16 a ⦃ result =>
      (fnearest_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_nearest a >>= runtime.interp.float.quiet32) ⦃ result =>
    (fnearest_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_nearest a as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_integral 32 (by omega) _ _)
    (nearest_reply_family _ _)

theorem unary32_sqrt_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U32) :
    runtime.interp.float.unary32 ops 6#u16 a ⦃ result =>
      (fsqrt_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄ := by
  unfold runtime.interp.float.unary32
  with_unfolding_all change (ops.f32_sqrt a >>= runtime.interp.float.quiet32) ⦃ result =>
    (fsqrt_ 32 (floatOfBits 32 a.val)).head?=some (floatOfBits 32 result.val) ⦄
  step with correct.f32_sqrt a as ⟨raw,outcome⟩
  exact quiet32_first_choice raw _ outcome (canonicalClosed_sqrt 32 (by omega) _)
    (sqrt_reply_family _ _)

theorem binary64_add_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 0#u16 a b ⦃ result =>
      (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_add a b >>= runtime.interp.float.quiet64) ⦃ result =>
    (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_add a b as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_add 64 (by omega) _ _)
    (add_reply_family _ _ _)

theorem binary64_sub_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 1#u16 a b ⦃ result =>
      (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_sub a b >>= runtime.interp.float.quiet64) ⦃ result =>
    (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_sub a b as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_sub 64 (by omega) _ _)
    (sub_reply_family _ _ _)

theorem binary64_mul_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 2#u16 a b ⦃ result =>
      (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_mul a b >>= runtime.interp.float.quiet64) ⦃ result =>
    (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_mul a b as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_mul 64 (by omega) _ _)
    (mul_reply_family _ _ _)

theorem binary64_div_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.binary64 ops 3#u16 a b ⦃ result =>
      (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.binary64
  with_unfolding_all change (ops.f64_div a b >>= runtime.interp.float.quiet64) ⦃ result =>
    (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_div a b as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_div 64 (by omega) _ _)
    (div_reply_family _ _ _)

theorem unary64_ceil_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 2#u16 a ⦃ result =>
      (fceil_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_ceil a >>= runtime.interp.float.quiet64) ⦃ result =>
    (fceil_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_ceil a as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_integral 64 (by omega) _ _)
    (ceil_reply_family _ _)

theorem unary64_floor_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 3#u16 a ⦃ result =>
      (ffloor_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_floor a >>= runtime.interp.float.quiet64) ⦃ result =>
    (ffloor_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_floor a as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_integral 64 (by omega) _ _)
    (floor_reply_family _ _)

theorem unary64_trunc_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 4#u16 a ⦃ result =>
      (ftrunc_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_trunc a >>= runtime.interp.float.quiet64) ⦃ result =>
    (ftrunc_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_trunc a as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_integral 64 (by omega) _ _)
    (trunc_reply_family _ _)

theorem unary64_nearest_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 5#u16 a ⦃ result =>
      (fnearest_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_nearest a >>= runtime.interp.float.quiet64) ⦃ result =>
    (fnearest_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_nearest a as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_integral 64 (by omega) _ _)
    (nearest_reply_family _ _)

theorem unary64_sqrt_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a : U64) :
    runtime.interp.float.unary64 ops 6#u16 a ⦃ result =>
      (fsqrt_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄ := by
  unfold runtime.interp.float.unary64
  with_unfolding_all change (ops.f64_sqrt a >>= runtime.interp.float.quiet64) ⦃ result =>
    (fsqrt_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 result.val) ⦄
  step with correct.f64_sqrt a as ⟨raw,outcome⟩
  exact quiet64_first_choice raw _ outcome (canonicalClosed_sqrt 64 (by omega) _)
    (sqrt_reply_family _ _)
theorem scalar_f32_convert_i32_s_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 178#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)]).head?=some (floatOfBits 32 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i32_s ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f32_convert_i32_u_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 179#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 32 32 .U (.mk_uN (UScalar.cast .U32 a).val)]).head?=some (floatOfBits 32 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i32_u ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f32_convert_i64_s_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 180#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)]).head?=some (floatOfBits 32 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i64_s ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f32_convert_i64_u_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 181#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 64 32 .U (.mk_uN a.val)]).head?=some (floatOfBits 32 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f32_convert_i64_u ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f64_convert_i32_s_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 183#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)]).head?=some (floatOfBits 64 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_s ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f64_convert_i32_u_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 184#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 32 64 .U (.mk_uN (UScalar.cast .U32 a).val)]).head?=some (floatOfBits 64 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_u ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f64_convert_i64_s_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 185#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 (UScalar.hcast .I64 a)).val)]).head?=some (floatOfBits 64 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_s ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f64_convert_i64_u_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 186#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ ([convert__ 64 64 .U (.mk_uN a.val)]).head?=some (floatOfBits 64 value.val) ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_u ops hf a b)
  rintro result ⟨value,returned,member⟩
  refine ⟨value,returned,?_⟩
  have same := List.mem_singleton.mp member
  simpa only [List.head?_cons,Option.some.injEq] using same.symm

theorem scalar_f32_demote_f64_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 182#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (demote__ 64 32 (floatOfBits 64 a.val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (ops.f32_demote_f64 a >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (demote__ 64 32 (floatOfBits 64 a.val)).head?=some (floatOfBits 32 value.val) ⦄
  simp only [lift, bind_ok]
  step with hf.f32_demote_f64 a as ⟨raw, hraw⟩
  step with quiet32_first_choice raw _ hraw (canonicalClosed_demote 64 32 (by omega) _) (demote_reply_family _ _ _) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_ceil_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 141#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fceil_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (141#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fceil_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_ceil_first_choice ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_floor_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 142#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (ffloor_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (142#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (ffloor_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_floor_first_choice ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_trunc_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 143#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (ftrunc_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (143#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (ftrunc_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_trunc_first_choice ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_nearest_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 144#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fnearest_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (144#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fnearest_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_nearest_first_choice ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_sqrt_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 145#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fsqrt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (145#u16 - 139#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => runtime.interp.float.unary32 ops index av >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fsqrt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with unary32_sqrt_first_choice ops hf (UScalar.cast .U32 a) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_add_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 146#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fadd_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (146#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fadd_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_add_first_choice ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_sub_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 147#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fsub_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (147#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fsub_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_sub_first_choice ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_mul_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 148#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fmul_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (148#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fmul_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_mul_first_choice ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f32_div_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 149#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fdiv_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (149#u16 - 146#u16 >>= fun index => lift (UScalar.cast .U32 a) >>= fun av => lift (UScalar.cast .U32 b) >>= fun bv => runtime.interp.float.binary32 ops index av bv >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fdiv_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val)).head?=some (floatOfBits 32 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  simp only [lift, bind_ok]
  step with binary32_div_first_choice ops hf (UScalar.cast .U32 a) (UScalar.cast .U32 b) as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  simpa only [U32.cast_U64_val_eq] using hvalue

theorem scalar_f64_ceil_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 155#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fceil_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (155#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fceil_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  step with unary64_ceil_first_choice ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_floor_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 156#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (ffloor_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (156#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (ffloor_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  step with unary64_floor_first_choice ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_trunc_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 157#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (ftrunc_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (157#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (ftrunc_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 4#u16 := by scalar_tac
  subst index
  step with unary64_trunc_first_choice ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_nearest_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 158#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fnearest_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (158#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fnearest_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 5#u16 := by scalar_tac
  subst index
  step with unary64_nearest_first_choice ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_sqrt_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 159#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fsqrt_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (159#u16 - 153#u16 >>= fun index => runtime.interp.float.unary64 ops index a >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fsqrt_ 64 (floatOfBits 64 a.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 6#u16 := by scalar_tac
  subst index
  step with unary64_sqrt_first_choice ops hf a as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_add_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 160#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (160#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 0#u16 := by scalar_tac
  subst index
  step with binary64_add_first_choice ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_sub_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 161#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (161#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 1#u16 := by scalar_tac
  subst index
  step with binary64_sub_first_choice ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_mul_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 162#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (162#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 2#u16 := by scalar_tac
  subst index
  step with binary64_mul_first_choice ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

theorem scalar_f64_div_first_choice {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 163#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (163#u16 - 160#u16 >>= fun index => runtime.interp.float.binary64 ops index a b >>= fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)).head?=some (floatOfBits 64 value.val) ⦄
  step as ⟨index, hi⟩
  have he : index = 3#u16 := by scalar_tac
  subst index
  step with binary64_div_first_choice ops hf a b as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

end Exec.Interp
