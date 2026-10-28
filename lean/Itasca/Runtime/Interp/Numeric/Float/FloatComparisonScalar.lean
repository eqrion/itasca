import Itasca.Runtime.Interp.Numeric.Float.FloatCompare

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

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
  rw [rawCompare_eq32 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_ne32 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_lt32 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_gt32 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_le32 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_ge32 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_eq64 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_ne64 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_lt64 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_gt64 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_le64 _ _ (by scalar_tac) (by scalar_tac)]
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
  rw [rawCompare_ge64 _ _ (by scalar_tac) (by scalar_tac)]
  refine ⟨_, rfl, ?_⟩
  simp [fge_, fgt_, fge_, fle_, flt_, feq_, fne_, Bool.toNat, proj_uN_0]
  all_goals split <;> simp_all

end Itasca.Runtime.Interp
