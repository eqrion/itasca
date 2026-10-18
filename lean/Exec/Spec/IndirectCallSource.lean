import Exec.Spec.TableAccess
namespace Exec.Spec
open SpecExt

/-- The generated indirect-call rule resolves exactly a function reference
whose signature matches the module type selected by the instruction. -/
def IndirectTarget (s : store) (f : frame) (table type position address : Nat) : Prop :=
  (fun_table ⟨s,f⟩ (.mk_uN table)).REFS[position]? = some (.REF_FUNC_ADDR address) ∧
    ∃ function,s.FUNCS[address]?=some function ∧ fun_type ⟨s,f⟩ (.mk_uN type)=function.TYPE

theorem indirect_target_unique {s f table type position a b}
    (first : IndirectTarget s f table type position a) (second : IndirectTarget s f table type position b) : a=b := by
  have equal := Option.some.inj (first.1.symm.trans second.1)
  cases equal
  rfl

theorem call_indirect_resolve (s : store) (f : frame) (table type position address : Nat)
    (hs : wf_store s) (hf : wf_frame f) (ht : table<2^32) (hy : type<2^32) (hp : position<2^32)
    (target : IndirectTarget s f table type position address) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ []
      ⟨⟨s,f⟩,[.CALL_ADDR address]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_11 _ _ (Segment.index_wf _ ht) (Segment.index_wf _ hy)⟩
  obtain ⟨inside,reference⟩ := List.getElem?_eq_some_iff.mp target.1
  obtain ⟨function,lookup,signature⟩ := target.2
  obtain ⟨issued,actual⟩ := List.getElem?_eq_some_iff.mp lookup
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_70 address))
  apply Step_read.call_indirect_call ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN table) (.mk_uN type) address
  · exact inside
  · simp [proj_num__0]
  · simpa only [proj_num__0,proj_uN_0,Option.get!,getElem!_pos (fun_table ⟨s,f⟩ (.mk_uN table)).REFS position inside] using reference
  · exact issued
  · simpa only [fun_funcinst,getElem!_pos s.FUNCS address issued,actual] using signature
  · exact input
  · exact .admininstr_case_70 _

theorem call_indirect_trap (s : store) (f : frame) (table type position : Nat)
    (hs : wf_store s) (hf : wf_frame f) (ht : table<2^32) (hy : type<2^32) (hp : position<2^32)
    (missing : ¬∃address,IndirectTarget s f table type position address) :
    StepH ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[Segment.i32 position,.CALL_INDIRECT (.mk_uN table) (.mk_uN type)]⟩ := by
    apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hp,.admininstr_case_11 _ _ (Segment.index_wf _ ht) (Segment.index_wf _ hy)⟩
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_73))
  apply Step_read.call_indirect_trap ⟨s,f⟩ (.mk_num__0 .I32 (.mk_uN position)) (.mk_uN table) (.mk_uN type) ?_ input .admininstr_case_73
  intro prior
  cases prior with
  | call_indirect_call_0 _ _ _ _ address inside numeric reference issued signature _ _ =>
    have inside' : position < (fun_table ⟨s,f⟩ (.mk_uN table)).REFS.length := inside
    have issued' : address < s.FUNCS.length := issued
    apply missing
    refine ⟨address,List.getElem?_eq_some_iff.mpr ⟨inside',?_⟩,s.FUNCS[address],List.getElem?_eq_getElem issued',?_⟩
    · simpa only [proj_num__0,proj_uN_0,Option.get!,getElem!_pos (fun_table ⟨s,f⟩ (.mk_uN table)).REFS position inside'] using reference
    · simpa only [fun_funcinst,getElem!_pos s.FUNCS address issued'] using signature
end Exec.Spec
