import Itasca.Runtime.Spec.TableAccess
namespace Itasca.Runtime.Spec
open SpecExt

/-- A refused table growth returns the WebAssembly unsigned failure sentinel. -/
theorem table_grow_fail_step (s : store) (f : frame) (index delta : Nat) (value : ref)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hd : delta < 2^32) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (2^32-1)]⟩ := by
  apply StepH.step
  apply Step.table_grow_fail
  · simpa using (fun_inv_signed_.fun_inv_signed__case_1 32 (-1) (by decide))
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.ref_wf _,Segment.i32_wf _ hd,.admininstr_case_51 _ (Segment.index_wf _ hx)⟩
  · apply wf_config_make hs hf
    simpa [Forall,Segment.i32] using Segment.i32_wf 4294967295 (by decide)

/-- A successful source table growth replaces the complete table instance and
returns its original length. -/
theorem table_grow_success_step (s : store) (f : frame) (index delta : Nat) (value : ref)
    (next : tableinst)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32) (hd : delta < 2^32)
    (mapped : index < f.MODULE.TABLES.length)
    (bounded : (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length < 2^32)
    (grown : fun_growtable (fun_table ⟨s,f⟩ (.mk_uN index)) delta value (some next))
    (fresh : wf_store {s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)}) :
    StepH ⟨⟨s,f⟩,[admininstr_ref value,Segment.i32 delta,.TABLE_GROW (.mk_uN index)]⟩ []
      ⟨⟨{s with TABLES := s.TABLES.modify f.MODULE.TABLES[index]! (fun _ => next)},f⟩,
        [Segment.i32 (fun_table ⟨s,f⟩ (.mk_uN index)).REFS.length]⟩ := by
  apply StepH.step
  apply Step.table_grow_succeed _ _ _ _ next (some next)
  · exact grown
  · exact fun_with_tableinst.fun_with_tableinst_case_0 s f (.mk_uN index) next mapped (.state_case_0 _ _ fresh hf)
  · simp
  · rfl
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.ref_wf _,Segment.i32_wf _ hd,.admininstr_case_51 _ (Segment.index_wf _ hx)⟩
  · apply wf_config_make fresh hf
    simpa [Forall,Segment.i32] using Segment.i32_wf _ bounded
end Itasca.Runtime.Spec
