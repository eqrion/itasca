import Exec.Spec.FloatTrunc
import Exec.Interp.Numeric.Float.FloatTruncScalar
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

def TruncSourceOutcome (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (input : fN) (result : core.result.Result U64 runtime.ExecError) : Prop :=
  let instructions := [admininstr.CONST (numtype_Fnn source) (.mk_num__1 source input),
    .CVTOP (numtype_Inn target) (numtype_Fnn source)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))]
  match result with
  | .Ok value => Step_pure instructions [.CONST (numtype_Inn target) (.mk_num__0 target (.mk_uN value.val))]
  | .Err (.Trap reason) => Step_pure instructions [.TRAP] ∧
      (reason = .IntegerOverflow ∨ reason = .InvalidConversionToInteger)
  | .Err _ => False

theorem truncOutcome_source (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
    (input : fN) (result : core.result.Result U64 runtime.ExecError)
    (inputWf : wf_fN (sizenn (numtype_Fnn source)) input)
    (effect : TruncOutcome (if saturating then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input) result) :
    TruncSourceOutcome source target sign saturating input result := by
  cases result with
  | Ok value => exact Spec.float_truncation_pure source target sign saturating input _ effect inputWf
  | Err error =>
    cases error <;> simp only [TruncOutcome] at effect
    case Trap reason =>
      exact ⟨Spec.float_truncation_pure source target sign saturating input none effect.1 inputWf, effect.2⟩

theorem scalar_i32_trunc_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 168#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .S false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .S false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 169#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .U false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .U false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 170#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .S false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .S false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 171#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .U false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .U false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 174#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .S false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .S false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 175#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .U false (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .U false _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 176#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .S false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .S false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 177#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .U false (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .U false _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 256#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .S true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .S true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 257#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I32 .U true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I32 .U true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 258#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .S true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .S true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i32_trunc_sat_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 259#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I32 .U true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i32_trunc_sat_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I32 .U true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f32_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 260#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .S true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f32_s ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .S true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f32_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 261#u16 a b ⦃ result =>
      TruncSourceOutcome .F32 .I64 .U true (floatOfBits 32 (UScalar.cast .U32 a).val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f32_u ops a b)
  intro result effect
  apply truncOutcome_source .F32 .I64 .U true _ result
  · exact floatOfBits_wf 32 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f64_s_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 262#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .S true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f64_s ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .S true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

theorem scalar_i64_trunc_sat_f64_u_source {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops 263#u16 a b ⦃ result =>
      TruncSourceOutcome .F64 .I64 .U true (floatOfBits 64 a.val) result ⦄ := by
  apply WP.spec_mono (scalar_i64_trunc_sat_f64_u ops a b)
  intro result effect
  apply truncOutcome_source .F64 .I64 .U true _ result
  · exact floatOfBits_wf 64 (by omega) _
  · exact effect

end Exec.Interp
