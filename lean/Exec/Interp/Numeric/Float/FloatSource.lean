import Exec.Interp.Numeric.Float.FloatSigns
import Exec.Spec.FloatSigns
import Exec.Spec.FloatPure

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
