import Exec.Spec.TableAccess
namespace Itasca.Runtime.Spec
open SpecExt

/-- Memory size returns the exact page count of the source memory. -/
theorem memory_size_step (s : store) (f : frame)
    (hs : wf_store s) (hf : wf_frame f)
    (aligned : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length % 65536 = 0)
    (bounded : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32) :
    StepH ⟨⟨s,f⟩,[.MEMORY_SIZE]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536)]⟩ := by
  have input : wf_config ⟨⟨s,f⟩,[.MEMORY_SIZE]⟩ :=
    wf_config_make hs hf (by simpa [Forall] using wf_admininstr.admininstr_case_62)
  have output := Segment.i32_wf ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536) bounded
  refine StepH.step (Step.read _ _ _ ?_ input (wf_config_make hs hf (by simpa [Forall] using output)))
  apply Step_read.memory_size
  · simp only [Ki,Nat.mul_assoc]
    norm_num
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero aligned)
  · exact input
  · exact output
  · exact Segment.index_wf 0 (by decide)
end Itasca.Runtime.Spec
