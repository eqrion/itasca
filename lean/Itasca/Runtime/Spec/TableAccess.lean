import Itasca.Runtime.Spec.TableInitSource
namespace Itasca.Runtime.Spec
open SpecExt

/-- Source table reads return the selected reference or the exact bounds trap. -/
theorem table_get_step (s : store) (f : frame) (index position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hp : position < 2^32) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.TABLE_GET (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,if position < (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length then
        [admininstr_ref (fun_table ⟨s,f⟩ (.mk_uN index)).REFS[position]!] else [.TRAP]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.TABLE_GET (.mk_uN index)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_48 _ (Segment.index_wf _ hx)⟩
  split
  · rename_i inside
    refine StepH.step (Step.read _ _ _ ?_ input ?_)
    · exact Step_read.table_get_val ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN index) inside
        (by simp [proj_num__0]) input
    · apply wf_config_make hs hf
      simpa [Forall] using Segment.ref_wf (fun_table ⟨s,f⟩ (.mk_uN index)).REFS[position]!
  · rename_i outside
    refine StepH.step (Step.read _ _ _ ?_ input ?_)
    · exact Step_read.table_get_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN index)
        (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0] using Nat.le_of_not_gt outside) input (.admininstr_case_73)
    · apply wf_config_make hs hf
      simpa [Forall] using wf_admininstr.admininstr_case_73

/-- Table size returns the exact unsigned element count. -/
theorem table_size_step (s : store) (f : frame) (index : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (bounded : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32) :
    StepH ⟨⟨s,f⟩,[.TABLE_SIZE (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[.TABLE_SIZE (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_50 _ (Segment.index_wf _ hx))
  have output := Segment.i32_wf (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length bounded
  exact StepH.step (Step.read _ _ _
    (Step_read.table_size ⟨s,f⟩ (.mk_uN index) _ rfl input output) input
    (wf_config_make hs hf (by simpa [Forall] using output)))
end Itasca.Runtime.Spec
