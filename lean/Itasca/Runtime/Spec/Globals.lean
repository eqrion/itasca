import Itasca.Runtime.Spec.TableInit

namespace Itasca.Runtime.Spec
open SpecExt

/-- Source global writes change a single value, retaining its declared type. -/
def globalWrite (s : store) (f : frame) (index : Nat) (value : val) : store :=
  {s with GLOBALS := s.GLOBALS.modify f.MODULE.GLOBALS[index]! (fun global => {global with VALUE := value})}

theorem globalWrite_wf (s : store) (f : frame) (index : Nat) (value : val)
    (hs : wf_store s) (hv : wf_val value) : wf_store (globalWrite s f index value) := by
  cases s with | MKstore funcs globals tables mems elems datas =>
  cases hs with | store_case_ _ _ _ _ _ _ hfn hg ht hm hd =>
  apply wf_store.store_case_ _ _ _ _ _ _ hfn _ ht hm hd
  apply Segment.forall_modify _ _ _ _ hg
  intro global _
  exact .globalinst_case_ _ _ hv

/-- The generated global-read rule resolves the exact instance/global lookup;
well-formedness of the selected value follows from the input store. -/
theorem global_get_step (s : store) (f : frame) (index address : Nat) (global : globalinst)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (mapped : f.MODULE.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some global) :
    StepH ⟨⟨s,f⟩,[.GLOBAL_GET (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,vals [global.VALUE]⟩ := by
  have hg : wf_globalinst global := by
    cases hs
    apply_assumption
    exact List.mem_of_getElem? found
  have hv : wf_val global.VALUE := by cases hg; assumption
  have input := wf_config_make hs hf (show Forall wf_admininstr [.GLOBAL_GET (.mk_uN index)] from by
    simpa [Forall] using wf_admininstr.admininstr_case_46 _ (Segment.index_wf index hx))
  have output := wf_config_vals hs hf (show Forall wf_val [global.VALUE] from by simpa [Forall] using hv)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  simpa [fun_global, proj_uN_0, List.getElem!_eq_getElem?_getD, mapped, found, vals] using
    Step_read.global_get ⟨s,f⟩ (.mk_uN index) input

/-- The generated global-write rule, including source well-formedness of the
updated store. Mutability and value typing belong to instruction typing. -/
theorem global_set_step (s : store) (f : frame) (index : Nat) (value : val)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (hv : wf_val value) (mapped : index < f.MODULE.GLOBALS.length) :
    StepH ⟨⟨s,f⟩,[admininstr_val value,.GLOBAL_SET (.mk_uN index)]⟩ []
      ⟨⟨globalWrite s f index value,f⟩,[]⟩ := by
  have outputWf := globalWrite_wf s f index value hs hv
  apply StepH.step
  apply Step.global_set
  · exact .fun_with_global_case_0 s f (.mk_uN index) value mapped
      (.state_case_0 _ _ outputWf hf)
  · apply wf_config_make hs hf
    intro instruction member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact wf_admininstr_val hv
    · exact .admininstr_case_47 _ (Segment.index_wf index hx)
  · exact wf_config_make outputWf hf (forall_nil _)
end Itasca.Runtime.Spec
