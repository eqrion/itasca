import Itasca.Runtime.Interp.Numeric.Float.FloatTruncInstruction
import Itasca.Runtime.Interp.Numeric.Float.FloatReinterpretSource
import Itasca.Runtime.Spec.FloatTrunc

/-!
Sections, each formerly its own module: FloatInstructionBasic, FloatInstructionComparison.
-/

/-! ## FloatInstructionBasic -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f32_abs_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .ABS)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .ABS) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_abs_source ops a b) (scalar_f32_abs_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_neg_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .NEG)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .NEG) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_neg_source ops a b) (scalar_f32_neg_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_ceil_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .CEIL)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .CEIL) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_ceil_source ops correct a b) (scalar_f32_ceil_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_floor_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .FLOOR)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .FLOOR) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_floor_source ops correct a b) (scalar_f32_floor_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_trunc_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .TRUNC)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .TRUNC) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_trunc_source ops correct a b) (scalar_f32_trunc_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_nearest_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .NEAREST)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .NEAREST) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_nearest_source ops correct a b) (scalar_f32_nearest_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_sqrt_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F32 .SQRT)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F32 .SQRT) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_sqrt_source ops correct a b) (scalar_f32_sqrt_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_add_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .ADD)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .ADD) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_add_source ops correct a b) (scalar_f32_add_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_sub_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .SUB)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .SUB) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_sub_source ops correct a b) (scalar_f32_sub_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_mul_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .MUL)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .MUL) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_mul_source ops correct a b) (scalar_f32_mul_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_div_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .DIV)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .DIV) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_div_source ops correct a b) (scalar_f32_div_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_min_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .MIN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .MIN) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_min_source ops a b) (scalar_f32_min_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_max_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .MAX)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .MAX) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_max_source ops a b) (scalar_f32_max_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_copysign_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F32 .COPYSIGN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F32 .COPYSIGN) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_copysign_source ops a b) (scalar_f32_copysign_bounded ops a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F32 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F32 .S) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i32_s_source ops correct a b) (scalar_f32_convert_i32_s_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F32 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F32 .U) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i32_u_source ops correct a b) (scalar_f32_convert_i32_u_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F32 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F32 .S) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i64_s_source ops correct a b) (scalar_f32_convert_i64_s_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f32_convert_i64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F32 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F32 .U) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_convert_i64_u_source ops correct a b) (scalar_f32_convert_i64_u_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f64_abs_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .ABS)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .ABS) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_abs_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_neg_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .NEG)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .NEG) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_neg_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_ceil_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .CEIL)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .CEIL) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ceil_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_floor_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .FLOOR)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .FLOOR) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_floor_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_trunc_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .TRUNC)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .TRUNC) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_trunc_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_nearest_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .NEAREST)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .NEAREST) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_nearest_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_sqrt_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.unary .F64 .SQRT)) a b ⦃ result =>
      FloatScalarOutcome (.unary .F64 .SQRT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_sqrt_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_add_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .ADD)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .ADD) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_add_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_sub_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .SUB)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .SUB) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_sub_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_mul_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .MUL)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .MUL) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_mul_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_div_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .DIV)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .DIV) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_div_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_min_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .MIN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .MIN) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_min_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_max_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .MAX)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .MAX) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_max_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_copysign_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.binary .F64 .COPYSIGN)) a b ⦃ result =>
      FloatScalarOutcome (.binary .F64 .COPYSIGN) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_copysign_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F64 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F64 .S) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_s_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I32 .F64 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I32 .F64 .U) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i32_u_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F64 .S)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F64 .S) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_s_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_convert_i64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.convert .I64 .F64 .U)) a b ⦃ result =>
      FloatScalarOutcome (.convert .I64 .F64 .U) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_convert_i64_u_source ops correct a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f32_demote_f64_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (correct : FloatOpsCorrect ops) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.demote)) a b ⦃ result =>
      FloatScalarOutcome (.demote) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_f32_demote_f64_source ops correct a b) (scalar_f32_demote_f64_bounded ops correct a b))
  rintro result ⟨⟨value, rfl, source⟩, ⟨other, same, bound, _⟩⟩
  cases same
  refine ⟨bound, ?_⟩
  try simp only [signed_roundtrip32, signed_roundtrip64] at source
  exact source

theorem scalar_f64_promote_f32_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.promote)) a b ⦃ result =>
      FloatScalarOutcome (.promote) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_promote_f32_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_f64_reinterpret_i64_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I64)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretInt .I64) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_reinterpret_i64_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

theorem scalar_i64_reinterpret_f64_instruction {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F64)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretFloat .F64) a b result ⦄ := by
  apply WP.spec_mono (scalar_i64_reinterpret_f64_source ops a b)
  rintro result ⟨value, rfl, source⟩
  refine ⟨?_, ?_⟩
  · change value.val < 2^64
    scalar_tac
  · try simp only [signed_roundtrip32, signed_roundtrip64] at source
    exact source

end Itasca.Runtime.Interp

end

/-! ## FloatInstructionComparison -/

section

/-!
Floating-point comparison instruction correspondence. Bounded comparison results establish each f32/f64 comparison instruction and its integer result representation.
-/

/-! ## Float Comparison Bounded -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

/-- Actual f32.eq dispatch takes the generated comparison step. -/
theorem scalar_f32_eq_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 91#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .EQ)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_eq ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases feq_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .EQ)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_12 _ _ wf
  exact Spec.float_comparison_pure .F32 .EQ (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.ne dispatch takes the generated comparison step. -/
theorem scalar_f32_ne_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 92#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .NE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ne ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fne_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .NE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_14 _ _ wf
  exact Spec.float_comparison_pure .F32 .NE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.lt dispatch takes the generated comparison step. -/
theorem scalar_f32_lt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 93#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .LT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_lt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases flt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .LT)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_16 _ _ wf
  exact Spec.float_comparison_pure .F32 .LT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.gt dispatch takes the generated comparison step. -/
theorem scalar_f32_gt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 94#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .GT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_gt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fgt_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .GT)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_18 _ _ wf
  exact Spec.float_comparison_pure .F32 .GT (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.le dispatch takes the generated comparison step. -/
theorem scalar_f32_le_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 95#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .LE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_le ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fle_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .LE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_20 _ _ wf
  exact Spec.float_comparison_pure .F32 .LE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f32.ge dispatch takes the generated comparison step. -/
theorem scalar_f32_ge_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 96#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)),
        .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val)), .RELOP .F32 (.mk_relop__1 .F32 .GE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f32_ge ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) := by
    rw [hvalue]
    cases fge_ 32 (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) <;> rfl
  have relation : fun_relop_ .F32 (.mk_relop__1 .F32 .GE)
      (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)) (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 b).val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_22 _ _ wf
  exact Spec.float_comparison_pure .F32 .GE (floatOfBits 32 (UScalar.cast .U32 a).val) (floatOfBits 32 (UScalar.cast .U32 b).val) value.val relation
    (floatOfBits_wf 32 (by omega) _) (floatOfBits_wf 32 (by omega) _) small

/-- Actual f64.eq dispatch takes the generated comparison step. -/
theorem scalar_f64_eq_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 97#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .EQ)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_eq ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases feq_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .EQ)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_13 _ _ wf
  exact Spec.float_comparison_pure .F64 .EQ (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.ne dispatch takes the generated comparison step. -/
theorem scalar_f64_ne_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 98#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .NE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ne ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fne_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .NE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_15 _ _ wf
  exact Spec.float_comparison_pure .F64 .NE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.lt dispatch takes the generated comparison step. -/
theorem scalar_f64_lt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 99#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .LT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_lt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases flt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .LT)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_17 _ _ wf
  exact Spec.float_comparison_pure .F64 .LT (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.gt dispatch takes the generated comparison step. -/
theorem scalar_f64_gt_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 100#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .GT)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_gt ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fgt_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .GT)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_19 _ _ wf
  exact Spec.float_comparison_pure .F64 .GT (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.le dispatch takes the generated comparison step. -/
theorem scalar_f64_le_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 101#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .LE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_le ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fle_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .LE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_21 _ _ wf
  exact Spec.float_comparison_pure .F64 .LE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

/-- Actual f64.ge dispatch takes the generated comparison step. -/
theorem scalar_f64_ge_source_bounded {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 102#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val < 2^32 ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)),
        .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 b.val)), .RELOP .F64 (.mk_relop__1 .F64 .GE)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (scalar_f64_ge ops a b)
  rintro result ⟨value, rfl, hvalue⟩
  have small : value.val < 2 ^ 32 := by
    rw [hvalue]
    simp only [feq_, fne_, flt_, fgt_, fle_, fge_]
    split <;> decide
  refine ⟨value, rfl, small, ?_⟩
  have output : uN.mk_uN value.val = fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) := by
    rw [hvalue]
    cases fge_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val) <;> rfl
  have relation : fun_relop_ .F64 (.mk_relop__1 .F64 .GE)
      (.mk_num__1 .F64 (floatOfBits 64 a.val)) (.mk_num__1 .F64 (floatOfBits 64 b.val))
      (some (.mk_num__0 .I32 (.mk_uN value.val))) := by
    have wf := Spec.unsigned_num_wf .I32 value.val small
    rw [output] at wf ⊢
    exact .fun_relop__case_23 _ _ wf
  exact Spec.float_comparison_pure .F64 .GE (floatOfBits 64 a.val) (floatOfBits 64 b.val) value.val relation
    (floatOfBits_wf 64 (by omega) _) (floatOfBits_wf 64 (by omega) _) small

end Itasca.Runtime.Interp

end

/-! ## Float Instruction Comparison -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f32_eq_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .EQ)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .EQ) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_eq_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_ne_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .NE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .NE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_ne_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_lt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .LT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .LT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_lt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_gt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .GT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .GT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_gt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_le_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .LE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .LE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_le_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_ge_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F32 .GE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F32 .GE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f32_ge_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_eq_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .EQ)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .EQ) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_eq_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_ne_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .NE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .NE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ne_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_lt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .LT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .LT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_lt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_gt_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .GT)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .GT) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_gt_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_le_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .LE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .LE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_le_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f64_ge_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.compare .F64 .GE)) a b ⦃ result =>
      FloatScalarOutcome (.compare .F64 .GE) a b result ⦄ := by
  apply WP.spec_mono (scalar_f64_ge_source_bounded ops a b)
  rintro result ⟨value, rfl, bound, source⟩
  exact ⟨bound, source⟩

theorem scalar_f32_reinterpret_i32_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I32)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretInt .I32) a b result ⦄ := by
  have run : runtime.interp.float.scalar ops (floatOpcode (.reinterpretInt .I32)) a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · change (UScalar.cast .U64 (UScalar.cast .U32 a)).val < 2^32
    scalar_tac
  · have source := Spec.f32_reinterpret_i32_pure (UScalar.cast .U32 a).val (by scalar_tac)
    simp only [U32.cast_U64_val_eq]
    exact source

theorem scalar_i32_reinterpret_f32_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F32)) a b ⦃ result =>
      FloatScalarOutcome (.reinterpretFloat .F32) a b result ⦄ := by
  have run : runtime.interp.float.scalar ops (floatOpcode (.reinterpretFloat .F32)) a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · change (UScalar.cast .U64 (UScalar.cast .U32 a)).val < 2^32
    scalar_tac
  · have source := Spec.i32_reinterpret_f32_pure (UScalar.cast .U32 a).val (by scalar_tac)
    simp only [U32.cast_U64_val_eq]
    exact source

end Itasca.Runtime.Interp

end

end
