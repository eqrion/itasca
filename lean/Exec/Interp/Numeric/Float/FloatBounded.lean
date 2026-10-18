import Exec.Interp.Numeric.Float.FloatSigns
import Exec.Interp.Numeric.Float.FloatMinMax
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform
@[step] theorem scalar_f32_convert_i32_s_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (hf : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops 178#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄ := by
  unfold runtime.interp.float.scalar
  with_unfolding_all change (lift (UScalar.hcast .I32 a) >>= fun arg => ops.f32_convert_i32_s arg >>= fun raw => runtime.interp.float.quiet32 raw >>= fun value => lift (UScalar.cast .U64 value) >>= fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) ⦃ result => ∃ value, result = .Ok value ∧ value.val < 2^32 ∧ floatOfBits 32 value.val ∈ [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val)] ⦄
  simp only [lift, bind_ok]
  step with hf.f32_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw, hraw⟩
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value, hvalue⟩
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
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value, hvalue⟩
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
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 64 32 (by omega) _ _) as ⟨value, hvalue⟩
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
  step with quiet32_sound raw _ hraw (canonicalClosed_convert 64 32 (by omega) _ _) as ⟨value, hvalue⟩
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
  step with quiet32_sound raw _ hraw (canonicalClosed_demote 64 32 (by omega) _) as ⟨value, hvalue⟩
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

end Exec.Interp
