import Exec.Interp.Numeric.Float.FloatSource
import Exec.Spec.FloatConvert

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
