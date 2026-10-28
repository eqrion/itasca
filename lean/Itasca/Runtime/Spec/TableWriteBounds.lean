import Itasca.Runtime.Spec.TableAccess
namespace Itasca.Runtime.Spec
open SpecExt

/-- The source table write reports its bounds trap before changing the store. -/
theorem table_set_trap_step (s : store) (f : frame) (index position : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hp : position < 2^32)
    (outside : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length ≤ position) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,admininstr_ref value,.TABLE_SET (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  apply StepH.step
  apply Step.table_set_trap
  · simp [proj_num__0]
  · exact outside
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,Segment.ref_wf _,.admininstr_case_49 _ (Segment.index_wf _ hx)⟩
  · exact wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_73)
end Itasca.Runtime.Spec
