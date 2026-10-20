import Exec.Spec.Typing.LocalGlobalWriteTyping
import Exec.Spec.Typing.TableWriteTyping
/-! Generated table writes preserve typed references, stores, frame environments, and stack prefixes. -/

namespace Exec.Spec
open SpecExt

theorem reference_value_inversion {s : store} (reference : ref) {type : reftype}
    (typed : Val_ok s (val_ref reference) (valtype_reftype type)) : Ref_ok s reference type := by
  generalize sameValue : val_ref reference=value at typed
  generalize sameType : valtype_reftype type=valueType at typed
  cases typed
  case numtype => cases reference <;> simp [val_ref] at sameValue
  case vectype => cases reference <;> simp [val_ref] at sameValue
  case reftype =>
    rename_i actual actualType _ _
    have referenceTyped : Ref_ok s actual actualType := by assumption
    have referenceEq : reference=actual := by
      cases reference <;> cases actual <;> simp_all [val_ref]
    have typeEq : type=actualType := by
      cases type <;> cases actualType <;> simp_all [valtype_reftype]
    cases referenceEq
    cases typeEq
    exact referenceTyped

theorem table_set_operand {s : store} {context : _root_.context} {instruction : admininstr} (index : idx)
    (condition : num_) (reference : ref) {params : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list params) (.mk_list [])))
    (same : instruction=.TABLE_SET index) (arguments : ResultsTyped s params [.CONST .I32 condition,val_ref reference]) :
    ∃ type limits, proj_uN_0 index<context.TABLES.length ∧
      context.TABLES[proj_uN_0 index]! = .mk_tabletype limits type ∧ Ref_ok s reference type := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i type limits _ _ _ _ _
    cases arguments with
    | cons _ rest =>
      cases rest with
      | cons referenceTyped rest =>
        exact ⟨type,limits,by assumption,by assumption,reference_value_inversion reference referenceTyped⟩
  all_goals cases same

theorem table_set_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (storeTyped : Store_ok s) (environment : FrameEnvironment s frame context) (index : idx)
    (condition : num_) (reference : ref) (position : Nat) {after : state}
    (updated : fun_with_table ⟨s,frame⟩ index position reference after) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 condition,admininstr_ref reference,.TABLE_SET index]
      (.mk_functype (.mk_list input) (.mk_list output))) : WriteTypingResult s after context [] input output := by
  have representation : admininstr_val (val_ref reference)=admininstr_ref reference := by cases reference <;> rfl
  rw [← representation] at typed
  change Instrs_ok2 s context (vals [.CONST .I32 condition,val_ref reference]++[.TABLE_SET index]) _ at typed
  obtain ⟨base,params,primitive,arguments,inputSub,outputSub⟩ := write_operands_effect typed rfl
  obtain ⟨type,limits,bound,typeEq,referenceTyped⟩ := table_set_operand index condition reference primitive rfl arguments
  obtain ⟨address,object,addressFound,found,objectType⟩ := environment.table_lookup index bound
  have actualAddress : frame.MODULE.TABLES[proj_uN_0 index]! = address := by
    simp only [List.getElem!_eq_getElem?_getD,addressFound,Option.getD_some]
  have actualObject : s.TABLES[address]! = object := by
    simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  have actualType : sourceTableElementType s.TABLES[address]!.TYPE=type := by
    rw [actualObject,objectType,typeEq]
    rfl
  have actualTyped : Ref_ok s reference (sourceTableElementType s.TABLES[address]!.TYPE) := by
    rw [actualType]
    exact referenceTyped
  have wf := instrs_ok2_wf typed
  cases updated
  have givenPost : wf_state ⟨{s with TABLES := s.TABLES.modify (frame.MODULE.TABLES[proj_uN_0 index]!) (fun object => {object with REFS := object.REFS.modify position (fun _ => reference)})},frame⟩ := by assumption
  have normalizedPost : wf_state ⟨sourceTableUpdate s address position reference,frame⟩ := by
    simpa only [sourceTableUpdate,actualAddress,list_modify_as_set] using givenPost
  have effect := table_update_store_typed storeTyped address (List.getElem?_eq_some_iff.mp found).1 position reference actualTyped
    (wf_state_parts normalizedPost).1
  simp only [WriteTypingResult,actualAddress,list_modify_as_set]
  exact ⟨effect.1,effect.2,FrameEnvironment.extend effect.1 environment,
    realize_write_result inputSub outputSub (instrs_identity (extend_store_wf effect.1).2 wf.2.1 [])⟩

end Exec.Spec
