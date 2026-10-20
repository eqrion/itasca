import Exec.Spec.Typing.LocalGlobalWriteTyping

/-! Generated segment drops preserve genuine source store typing, old frame
environments, and the retained operand prefix. -/

namespace Exec.Spec
open SpecExt

theorem moduleinst_segment_bounds {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) :
    module.DATAS.length=context.DATAS.length ∧ Forall (fun address => address<s.DATAS.length) module.DATAS ∧
    module.ELEMS.length=context.ELEMS.length ∧ Forall (fun address => address<s.ELEMS.length) module.ELEMS := by
  cases typed
  exact ⟨by assumption,by assumption,by assumption,by assumption⟩

theorem data_empty_extends (object : datainst) (typed : wf_datainst object) :
    Extend_datainst object {object with BYTES := []} := by
  cases object
  exact .mk_Extend_datainst _ [] (Or.inr rfl) typed (.datainst_case_ _ (by simp [Forall]))

theorem element_empty_extends (object : eleminst) : Extend_eleminst object {object with REFS := []} := by
  cases object
  exact .mk_Extend_eleminst _ _ [] (Or.inr rfl)

def sourceDataDrop (s : store) (index : Nat) : store := {s with DATAS := s.DATAS.set index ⟨[]⟩}

def sourceElementDrop (s : store) (index : Nat) : store :=
  {s with ELEMS := s.ELEMS.set index {s.ELEMS[index]! with REFS := []}}

theorem data_drop_store_typed {s : store} (typed : Store_ok s) (index : Nat) (bound : index<s.DATAS.length)
    (postWf : wf_store (sourceDataDrop s index)) : Extend_store s (sourceDataDrop s index) ∧ Store_ok (sourceDataDrop s index) := by
  have components := source_store_components typed
  have member : s.DATAS[index]! ∈ s.DATAS := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound
  have oldTyped := components.data _ member
  have oldWf : wf_datainst s.DATAS[index]! := by
    generalize objectEq : s.DATAS[index]! = object at oldTyped ⊢
    cases oldTyped
    assumption
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s (sourceDataDrop s index) :=
    extend_store_set_data s index _ storeWf postWf (fun _ => data_empty_extends _ oldWf)
  refine ⟨extension,?_⟩
  apply source_store_data_set typed extension index ⟨[]⟩ rfl
  exact .mk_Datainst_ok _ [] (by decide) postWf (.datainst_case_ _ (by simp [Forall]))

theorem element_drop_store_typed {s : store} (typed : Store_ok s) (index : Nat)
    (postWf : wf_store (sourceElementDrop s index)) :
    Extend_store s (sourceElementDrop s index) ∧ Store_ok (sourceElementDrop s index) := by
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s (sourceElementDrop s index) :=
    extend_store_set_elem s index _ storeWf postWf (fun _ => element_empty_extends _)
  refine ⟨extension,?_⟩
  apply source_store_element_set typed extension index _ rfl
  exact .mk_Eleminst_ok _ _ [] (by simp [Forall]) (by decide) postWf

theorem data_drop_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx)
    {after : state} (updated : fun_with_data ⟨s,frame⟩ index [] after) {input output : List valtype}
    (typed : Instrs_ok2 s context [.DATA_DROP index] (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [] input output := by
  change Instrs_ok2 s context (vals []++[.DATA_DROP index]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  have moduleBounds := (moduleinst_segment_bounds environment.moduleTyped).2.1
  have wf := instrs_ok2_wf typed
  cases updated
  have moduleIndexBound : proj_uN_0 index<frame.MODULE.DATAS.length := by assumption
  have member : frame.MODULE.DATAS[proj_uN_0 index]! ∈ frame.MODULE.DATAS := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem moduleIndexBound,Option.getD_some] using List.getElem_mem moduleIndexBound
  have addressBound := moduleBounds _ member
  have givenPost : wf_state ⟨{s with DATAS := s.DATAS.modify (frame.MODULE.DATAS[proj_uN_0 index]!) (fun object => {object with BYTES := []})},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨sourceDataDrop s frame.MODULE.DATAS[proj_uN_0 index]!,frame⟩ := by
    simpa only [sourceDataDrop,list_modify_as_set] using givenPost
  have effect := data_drop_store_typed storeTyped _ addressBound (wf_state_parts normalizedPost).1
  simp only [WriteTypingResult,list_modify_as_set]
  exact ⟨effect.1,effect.2,FrameEnvironment.extend effect.1 environment,
    realize_write_result inputSub outputSub (instrs_identity (extend_store_wf effect.1).2 wf.2.1 [])⟩

theorem element_drop_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx)
    {after : state} (updated : fun_with_elem ⟨s,frame⟩ index [] after) {input output : List valtype}
    (typed : Instrs_ok2 s context [.ELEM_DROP index] (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [] input output := by
  change Instrs_ok2 s context (vals []++[.ELEM_DROP index]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  have wf := instrs_ok2_wf typed
  cases updated
  have givenPost : wf_state ⟨{s with ELEMS := s.ELEMS.modify (frame.MODULE.ELEMS[proj_uN_0 index]!) (fun object => {object with REFS := []})},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨sourceElementDrop s frame.MODULE.ELEMS[proj_uN_0 index]!,frame⟩ := by
    simpa only [sourceElementDrop,list_modify_as_set] using givenPost
  have effect := element_drop_store_typed storeTyped _ (wf_state_parts normalizedPost).1
  simp only [WriteTypingResult,list_modify_as_set]
  exact ⟨effect.1,effect.2,FrameEnvironment.extend effect.1 environment,
    realize_write_result inputSub outputSub (instrs_identity (extend_store_wf effect.1).2 wf.2.1 [])⟩

end Exec.Spec
