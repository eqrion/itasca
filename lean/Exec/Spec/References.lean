import Exec.Spec.TableInitSource
namespace Itasca.Runtime.Spec
open SpecExt

def referenceIsNull : ref → Nat
  | .REF_NULL _ => 1
  | _ => 0

/-- Nullness follows the generated positive and negative pure reduction
rules, including the negative rule's exclusion premise. -/
theorem ref_is_null_pure (value : ref) :
    Step_pure [admininstr_ref value,.REF_IS_NULL] [Segment.i32 (referenceIsNull value)] := by
  cases value with
  | REF_NULL ty =>
    exact .ref_is_null_true _ ty rfl .admininstr_case_42 (Segment.i32_wf 1 (by decide))
  | REF_FUNC_ADDR address =>
    apply Step_pure.ref_is_null_false _ _ .admininstr_case_42 (Segment.i32_wf 0 (by decide))
    intro excluded
    generalize equation : [admininstr_ref (ref.REF_FUNC_ADDR address),admininstr.REF_IS_NULL] = instructions at excluded
    cases excluded with
    | ref_is_null_true_0 value ty equality opcode result => subst value; simp [admininstr_ref] at equation
  | REF_HOST_ADDR address =>
    apply Step_pure.ref_is_null_false _ _ .admininstr_case_42 (Segment.i32_wf 0 (by decide))
    intro excluded
    generalize equation : [admininstr_ref (ref.REF_HOST_ADDR address),admininstr.REF_IS_NULL] = instructions at excluded
    cases excluded with
    | ref_is_null_true_0 value ty equality opcode result => subst value; simp [admininstr_ref] at equation

theorem ref_is_null_step (s : store) (f : frame) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,.REF_IS_NULL]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (referenceIsNull value)]⟩ := by
  refine StepH.step (Step.pure _ _ _ (ref_is_null_pure value) ?_ ?_)
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.ref_wf value,.admininstr_case_42⟩
  · apply wf_config_make hs hf
    have bound : referenceIsNull value < 2^32 := by cases value <;> simp [referenceIsNull]
    simpa [Forall] using Segment.i32_wf _ bound
end Itasca.Runtime.Spec
