import Itasca.Runtime.Spec.References
namespace Itasca.Runtime.Spec
open SpecExt

/-- Source REF_FUNC resolves the function address in the current instance. -/
theorem ref_func_step (s : store) (f : frame) (index address : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hx : index < 2^32)
    (mapped : f.MODULE.FUNCS[index]? = some address) :
    StepH ⟨⟨s,f⟩,[.REF_FUNC (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.REF_FUNC_ADDR address]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[.REF_FUNC (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_41 _ (Segment.index_wf _ hx))
  have output := wf_admininstr.admininstr_case_68 address
  have lookup : (fun_funcaddr ⟨s,f⟩)[index]! = address := by
    simp [fun_funcaddr,List.getElem!_eq_getElem?_getD,mapped]
  refine StepH.step (Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using output)))
  have step := Step_read.ref_func ⟨s,f⟩ (.mk_uN index)
    (by simpa [fun_funcaddr,proj_uN_0] using (List.getElem?_eq_some_iff.mp mapped).1) input
    (wf_admininstr.admininstr_case_68 _)
  simpa only [proj_uN_0,lookup] using step
end Itasca.Runtime.Spec
