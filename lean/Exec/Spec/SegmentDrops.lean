import Exec.Spec.Wf
import Exec.Spec.Steps
import Mathlib.Tactic

namespace Itasca.Runtime.Spec
open SpecExt

def droppedDataStore (s : store) (f : frame) (index : Nat) : store :=
  {s with DATAS := s.DATAS.modify f.MODULE.DATAS[index]! (fun data => {data with BYTES := []})}

def droppedElementStore (s : store) (f : frame) (index : Nat) : store :=
  {s with ELEMS := s.ELEMS.modify f.MODULE.ELEMS[index]! (fun element => {element with REFS := []})}

theorem data_drop_step (s : store) (f : frame) (index : Nat)
    (old : wf_store s) (ambient : wf_frame f) (encoded : index < 2^32)
    (mapped : index < f.MODULE.DATAS.length) (fresh : wf_store (droppedDataStore s f index)) :
    StepH ⟨⟨s,f⟩,[.DATA_DROP (.mk_uN index)]⟩ [] ⟨⟨droppedDataStore s f index,f⟩,[]⟩ := by
  have update : fun_with_data ⟨s,f⟩ (.mk_uN index) [] ⟨droppedDataStore s f index,f⟩ :=
    .fun_with_data_case_0 s f (.mk_uN index) [] mapped (.state_case_0 _ _ fresh ambient)
  apply StepH.step
  apply Step.data_drop _ _ _ update
  · apply wf_config_make old ambient
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact .admininstr_case_67 _ (wf_uN.uN_case_0 32 index (by norm_num; omega))
  · exact wf_config_make fresh ambient (by simp [Forall])

theorem element_drop_step (s : store) (f : frame) (index : Nat)
    (old : wf_store s) (ambient : wf_frame f) (encoded : index < 2^32)
    (mapped : index < f.MODULE.ELEMS.length) (fresh : wf_store (droppedElementStore s f index)) :
    StepH ⟨⟨s,f⟩,[.ELEM_DROP (.mk_uN index)]⟩ [] ⟨⟨droppedElementStore s f index,f⟩,[]⟩ := by
  have update : fun_with_elem ⟨s,f⟩ (.mk_uN index) [] ⟨droppedElementStore s f index,f⟩ :=
    .fun_with_elem_case_0 s f (.mk_uN index) [] mapped (.state_case_0 _ _ fresh ambient)
  apply StepH.step
  apply Step.elem_drop _ _ _ update
  · apply wf_config_make old ambient
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact .admininstr_case_55 _ (wf_uN.uN_case_0 32 index (by norm_num; omega))
  · exact wf_config_make fresh ambient (by simp [Forall])

end Itasca.Runtime.Spec
