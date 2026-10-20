import Exec.Spec.Choices.WriteOperands
import Exec.Spec.Typing.FrameWriteSupport
import Exec.Spec.Typing.GlobalWriteTyping
/-! Generated local/global setters preserve semantic stores, frame environments, and stack typing. -/

namespace Exec.Spec
open SpecExt

def WriteTypingResult (before : store) (after : state) (context : _root_.context)
    (body : List admininstr) (input output : List valtype) : Prop :=
  match after with
  | ⟨store,frame⟩ => Extend_store before store ∧ Store_ok store ∧ FrameEnvironment store frame context ∧
      Instrs_ok2 store context body (.mk_functype (.mk_list input) (.mk_list output))

theorem FrameEnvironment.set_local {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context) (index : Nat) (bound : index<context.LOCALS.length)
    (value : val) (typed : Val_ok s value context.LOCALS[index]!) :
    FrameEnvironment s {frame with LOCALS := frame.LOCALS.set index value} context :=
  ⟨environment.moduleTyped,resultsTyped_set environment.locals index bound typed⟩

theorem local_set_operand {s : store} {context : _root_.context} {instruction : admininstr} (index : idx)
    {params : List valtype} {value : val}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list params) (.mk_list [])))
    (same : instruction=.LOCAL_SET index) (arguments : ResultsTyped s params [value]) :
    proj_uN_0 index<context.LOCALS.length ∧ Val_ok s value context.LOCALS[proj_uN_0 index]! := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type _ _ _ _
    have bound : proj_uN_0 index<context.LOCALS.length := by assumption
    have selected : context.LOCALS[proj_uN_0 index]! = type := by assumption
    cases arguments with
    | cons valueTyped rest =>
      rw [selected]
      exact ⟨bound,valueTyped⟩
  all_goals cases same

theorem local_set_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx) (value : val)
    {after : state} (updated : fun_with_local ⟨s,frame⟩ index value after) {input output : List valtype}
    (typed : Instrs_ok2 s context [admininstr_val value,.LOCAL_SET index] (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [] input output := by
  change Instrs_ok2 s context (vals [value]++[.LOCAL_SET index]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  obtain ⟨bound,valueTyped⟩ := local_set_operand index primitive rfl arguments
  have wf := instrs_ok2_wf typed
  have changed := environment.set_local (proj_uN_0 index) bound value valueTyped
  cases updated
  rw [List.set_eq_modify] at changed
  exact ⟨extend_store_refl _ wf.1,storeTyped,changed,
    realize_write_result inputSub outputSub (instrs_identity wf.1 wf.2.1 [])⟩

theorem global_set_operand {s : store} {context : _root_.context} {instruction : admininstr} (index : idx)
    {params : List valtype} {value : val}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list params) (.mk_list [])))
    (same : instruction=.GLOBAL_SET index) (arguments : ResultsTyped s params [value]) :
    ∃ type, proj_uN_0 index<context.GLOBALS.length ∧
      context.GLOBALS[proj_uN_0 index]! = .mk_globaltype (some .MUT) type ∧ Val_ok s value type := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type _ _ _ _
    cases arguments with
    | cons valueTyped rest =>
      exact ⟨type,by assumption,by assumption,valueTyped⟩
  all_goals cases same

theorem global_set_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx) (value : val)
    {after : state} (updated : fun_with_global ⟨s,frame⟩ index value after) {input output : List valtype}
    (typed : Instrs_ok2 s context [admininstr_val value,.GLOBAL_SET index] (.mk_functype (.mk_list input) (.mk_list output))) :
    WriteTypingResult s after context [] input output := by
  change Instrs_ok2 s context (vals [value]++[.GLOBAL_SET index]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  obtain ⟨type,bound,typeEq,valueTyped⟩ := global_set_operand index primitive rfl arguments
  obtain ⟨address,object,addressFound,found,objectType⟩ := environment.global_lookup index bound
  have actualAddress : frame.MODULE.GLOBALS[proj_uN_0 index]! = address := by
    simp only [List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some]
  have actualObject : s.GLOBALS[address]! = object := by
    simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  have actualType : s.GLOBALS[address]!.TYPE=.mk_globaltype (some .MUT) type := by
    rw [actualObject]
    exact objectType.trans typeEq
  have wf := instrs_ok2_wf typed
  cases updated
  have givenPost : wf_state ⟨{s with GLOBALS := s.GLOBALS.modify (frame.MODULE.GLOBALS[proj_uN_0 index]!) (fun object => {object with VALUE := value})},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨sourceGlobalUpdate s address value,frame⟩ := by
    simpa only [sourceGlobalUpdate,actualAddress,list_modify_as_set] using givenPost
  have postWf := (wf_state_parts normalizedPost).1
  have effect := global_update_store_typed storeTyped address (List.getElem?_eq_some_iff.mp found).1 value type actualType valueTyped postWf
  simp only [WriteTypingResult,actualAddress,list_modify_as_set]
  exact ⟨effect.1,effect.2,FrameEnvironment.extend effect.1 environment,
    realize_write_result inputSub outputSub (instrs_identity (extend_store_wf effect.1).2 wf.2.1 [])⟩

end Exec.Spec
