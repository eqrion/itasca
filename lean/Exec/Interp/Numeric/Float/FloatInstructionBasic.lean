import Exec.Interp.Numeric.Float.FloatInstructionOutcome
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
