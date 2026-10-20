import Exec.Interp.Numeric.Float.FloatFirstChoice
import Exec.Interp.Numeric.Float.FloatPromotionFirst
import Exec.Spec.NumericPolicyMatching
import Exec.Spec.FloatPromote
namespace Exec.Interp
open Aeneas Aeneas.Std Exec.Spec SpecExt SpecExt.Builtins SpecExt.Builtins.Float Platform

theorem scalar_f64_promote_f32_chosen {F : Type} (ops : runtime.platform.FloatOps F) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 187#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ ChosenNumeric firstNumericChoice occurrence
        (.convert .F32 .F64 (.mk_cvtop___3 .F32 .F64 .PROMOTE)
          (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)))
        (some (.mk_num__1 .F64 (floatOfBits 64 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f64_promote_f32_first_choice ops a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  apply chosen_numeric_from_head occurrence
  · apply NumericRequest.Allowed.convert (Spec.float_promote_relation _)
    · constructor
      exact Spec.float_num_wf .F32 _ (floatOfBits_wf 32 (by omega) _)
    · exact wf_admininstr_instr (.instr_case_18 .F64 .F32 (.mk_cvtop___3 .F32 .F64 .PROMOTE)
        (.cvtop___case_3 .F32 .F64 .F32 .F64 .PROMOTE
          (.cvtop__Fnn_1_Fnn_2_case_0 .F32 .F64 (by decide)) rfl rfl) (by decide))
    · exact Spec.numeric_cvtop_results_wf (Spec.float_promote_relation _)
  · simp only [List.head?_map,head,Option.map_some]

theorem scalar_f32_demote_f64_chosen {F : Type} (ops : runtime.platform.FloatOps F) (correct : FloatOpsCorrect ops) (occurrence : Nat) (a b : U64) :
    runtime.interp.float.scalar ops 182#u16 a b ⦃ result =>
      ∃ value, result=.Ok value ∧ ChosenNumeric firstNumericChoice occurrence
        (.convert .F64 .F32 (.mk_cvtop___3 .F64 .F32 .DEMOTE)
          (.mk_num__1 .F64 (floatOfBits 64 a.val)))
        (some (.mk_num__1 .F32 (floatOfBits 32 value.val))) ⦄ := by
  apply WP.spec_mono (scalar_f32_demote_f64_first_choice ops correct a b)
  rintro result ⟨value,returned,head⟩
  refine ⟨value,returned,?_⟩
  apply chosen_numeric_from_head occurrence
  · apply NumericRequest.Allowed.convert (Spec.float_demote_relation _)
    · constructor
      exact Spec.float_num_wf .F64 _ (floatOfBits_wf 64 (by omega) _)
    · exact wf_admininstr_instr (.instr_case_18 .F32 .F64 (.mk_cvtop___3 .F64 .F32 .DEMOTE)
        (.cvtop___case_3 .F64 .F32 .F64 .F32 .DEMOTE
          (.cvtop__Fnn_1_Fnn_2_case_1 .F64 .F32 (by decide)) rfl rfl) (by decide))
    · exact Spec.numeric_cvtop_results_wf (Spec.float_demote_relation _)
  · simp only [List.head?_map,head,Option.map_some]
end Exec.Interp
