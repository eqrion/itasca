import Exec.Interp.Numeric.Float.FloatInstructionOutcome
import Exec.Interp.Numeric.Float.FloatTruncSource
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem truncOutcome_value_bound (source : Fnn) (target : Inn) (sign : sx) (sat : Bool)
    (input : fN) (value : U64)
    (effect : TruncOutcome (if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input) (.Ok value)) :
    value.val < 2^sizenn (numtype_Inn target) := by
  have valid : Forall (fun result => wf_num_ (numtype_Inn target) (.mk_num__0 target result))
      (if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign input).toList := by
    cases sat
    · exact Spec.float_trunc_results_wf _ target sign input
    · exact Spec.float_trunc_sat_results_wf _ target sign input
  change _ = some (uN.mk_uN value.val) at effect
  rw [effect] at valid
  exact Abs.Float.integer_number_bound target value.val (valid _ (by simp))

theorem trunc_instruction_result (source : Fnn) (target : Inn) (sign : sx) (sat : Bool)
    (a b : U64) (result : core.result.Result U64 runtime.ExecError)
    (semantic : TruncOutcome (if sat then trunc_sat__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign
        (floatOfBits (sizenn (numtype_Fnn source)) (floatInput (numtype_Fnn source) a))
      else trunc__ (sizenn (numtype_Fnn source)) (sizenn (numtype_Inn target)) sign
        (floatOfBits (sizenn (numtype_Fnn source)) (floatInput (numtype_Fnn source) a))) result)
    (sourceStep : TruncSourceOutcome source target sign sat
      (floatOfBits (sizenn (numtype_Fnn source)) (floatInput (numtype_Fnn source) a)) result) :
    FloatScalarOutcome (.truncate source target sign sat) a b result := by
  cases result with
  | Ok value =>
    have bound := truncOutcome_value_bound source target sign sat _ value semantic
    cases source <;> cases target <;> exact ⟨bound, sourceStep⟩
  | Err error =>
    cases error <;> simp only [TruncSourceOutcome] at sourceStep
    case Trap reason =>
      cases source <;> cases target <;> exact sourceStep

theorem scalar_i32_trunc_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f32_s ops a b) (scalar_i32_trunc_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .S false a b result effect.1 effect.2

theorem scalar_i32_trunc_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f32_u ops a b) (scalar_i32_trunc_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .U false a b result effect.1 effect.2

theorem scalar_i32_trunc_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f64_s ops a b) (scalar_i32_trunc_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .S false a b result effect.1 effect.2

theorem scalar_i32_trunc_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_f64_u ops a b) (scalar_i32_trunc_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .U false a b result effect.1 effect.2

theorem scalar_i64_trunc_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f32_s ops a b) (scalar_i64_trunc_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .S false a b result effect.1 effect.2

theorem scalar_i64_trunc_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f32_u ops a b) (scalar_i64_trunc_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .U false a b result effect.1 effect.2

theorem scalar_i64_trunc_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .S false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .S false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f64_s ops a b) (scalar_i64_trunc_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .S false a b result effect.1 effect.2

theorem scalar_i64_trunc_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .U false)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .U false) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_f64_u ops a b) (scalar_i64_trunc_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .U false a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f32_s ops a b) (scalar_i32_trunc_sat_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .S true a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I32 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I32 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f32_u ops a b) (scalar_i32_trunc_sat_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I32 .U true a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f64_s ops a b) (scalar_i32_trunc_sat_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .S true a b result effect.1 effect.2

theorem scalar_i32_trunc_sat_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I32 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I32 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i32_trunc_sat_f64_u ops a b) (scalar_i32_trunc_sat_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I32 .U true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f32_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f32_s ops a b) (scalar_i64_trunc_sat_f32_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .S true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f32_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F32 .I64 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F32 .I64 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f32_u ops a b) (scalar_i64_trunc_sat_f32_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F32 .I64 .U true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f64_s_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .S true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .S true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f64_s ops a b) (scalar_i64_trunc_sat_f64_s_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .S true a b result effect.1 effect.2

theorem scalar_i64_trunc_sat_f64_u_instruction {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.float.scalar ops (floatOpcode (.truncate .F64 .I64 .U true)) a b ⦃ result =>
      FloatScalarOutcome (.truncate .F64 .I64 .U true) a b result ⦄ := by
  apply WP.spec_mono (spec_both (scalar_i64_trunc_sat_f64_u ops a b) (scalar_i64_trunc_sat_f64_u_source ops a b))
  intro result effect
  exact trunc_instruction_result .F64 .I64 .U true a b result effect.1 effect.2

end Exec.Interp
