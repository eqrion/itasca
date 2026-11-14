import Itasca.Runtime.Interp.Numeric.Float.FloatPromote
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Interp.Numeric.Float

/-!
Sections, each formerly its own module: FloatComparisonScalar, FloatSource, FloatConvertSource, FloatMinMaxSource, FloatPromoteSource, FloatReinterpretSource.
-/

/-! ## FloatComparisonScalar -/

section

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

end

/-! ## FloatSource -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

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
  · exact Spec.float_f32_abs_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_neg_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_ceil_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_floor_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_trunc_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_nearest_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_sqrt_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_add_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_sub_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_mul_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_div_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_copysign_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f64_abs_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_neg_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_ceil_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_floor_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_trunc_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_nearest_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_sqrt_relation (floatOfBits 64 a.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_add_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_sub_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_mul_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_div_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_copysign_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

end Itasca.Runtime.Interp

end

/-! ## FloatConvertSource -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

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
  · exact Spec.float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) _)
  · exact Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) _)
  · exact .cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Runtime.Interp

end

/-! ## FloatMinMaxSource -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

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
  · exact Spec.float_f32_min_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f32_max_relation (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _
  · exact floatOfBits_wf 32 (by omega) _

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
  · exact Spec.float_f64_min_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

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
  · exact Spec.float_f64_max_relation (floatOfBits 64 a.val) (floatOfBits 64 b.val) (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _)
  · exact chosen
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _
  · exact floatOfBits_wf 64 (by omega) _

end Itasca.Runtime.Interp

end

/-! ## FloatPromoteSource -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

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
  · exact Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) _)
  · exact Spec.float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) _)
  · exact .cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_0 _ _ (by decide)) rfl rfl
  · decide

end Itasca.Runtime.Interp

end

/-! ## FloatReinterpretSource -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

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

end Itasca.Runtime.Interp

end
