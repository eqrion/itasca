import Exec.Spec.Typing.BulkReadTyping
import Exec.Spec.Typing.ElementReadTyping

/-! Recursive table initialization preserves semantic typing using the actual
element segment reference type and the destination table declaration. -/

namespace Exec.Spec
open SpecExt

theorem table_init_success_typing_preserved {s : store} {frame : _root_.frame} {context : _root_.context}
    (environment : FrameEnvironment s frame context)
    (destination source count nextDestination nextSource nextCount : num_) (tableIndex elementIndex : idx) (position : Nat)
    (elementBound : position<(fun_elem ⟨s,frame⟩ elementIndex).REFS.length)
    (setWf : wf_admininstr (.TABLE_SET tableIndex))
    (writeWf : wf_admininstr (.CONST .I32 destination))
    (nextDestinationWf : wf_admininstr (.CONST .I32 nextDestination)) (nextSourceWf : wf_admininstr (.CONST .I32 nextSource))
    (nextCountWf : wf_admininstr (.CONST .I32 nextCount)) {input output : List valtype}
    (typed : Instrs_ok2 s context [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count,.TABLE_INIT tableIndex elementIndex]
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.CONST .I32 destination,admininstr_ref (fun_elem ⟨s,frame⟩ elementIndex).REFS[position]!,
      .TABLE_SET tableIndex,.CONST .I32 nextDestination,.CONST .I32 nextSource,.CONST .I32 nextCount,.TABLE_INIT tableIndex elementIndex]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  change Instrs_ok2 s context (vals [.CONST .I32 destination,.CONST .I32 source,.CONST .I32 count]++[.TABLE_INIT tableIndex elementIndex]) _ at typed
  apply value_operation_at_context typed
  intro params results primitive
  generalize same : admininstr.TABLE_INIT tableIndex elementIndex=instruction at primitive
  have storeWf : wf_store s := by cases primitive <;> assumption
  have contextWf : wf_context context := by cases primitive <;> assumption
  cases primitive
  case plain =>
    rename_i operator _ _ _ operatorTyped
    cases operator <;> simp [admininstr_instr] at same
    rcases same with ⟨tableEq,elementEq⟩
    cases tableEq
    cases elementEq
    have originalInit := operatorTyped
    cases operatorTyped
    rename_i limits type _ _ _ _ _ _ _
    have setSourceWf := source_instr_wf_of_admin (instruction := .TABLE_SET tableIndex) setWf
    have storeTyped : Instr_ok context (.TABLE_SET tableIndex)
        (.mk_functype (.mk_list [.I32,valtype_reftype type]) (.mk_list [])) := by
      apply Instr_ok.table_set <;> assumption
    have elementContextBound : proj_uN_0 elementIndex<context.ELEMS.length := by assumption
    have elementType : context.ELEMS[proj_uN_0 elementIndex]! = type := by assumption
    have refs := environment.element_references elementIndex elementContextBound elementType
    have member : (fun_elem ⟨s,frame⟩ elementIndex).REFS[position]! ∈ (fun_elem ⟨s,frame⟩ elementIndex).REFS := by
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem elementBound,Option.getD_some] using List.getElem_mem elementBound
    have referenceTyped := refs _ member
    refine ⟨rfl,fun _ => ?_⟩
    have writeValue := Val_ok.numtype s .I32 destination storeWf (val_wf_of_admin writeWf)
    have referenceValue := Val_ok.reftype s _ _ referenceTyped storeWf
    have first := instruction_on_values storeWf storeTyped (.cons writeValue (.cons referenceValue .nil))
    have destValue := Val_ok.numtype s .I32 nextDestination storeWf (val_wf_of_admin nextDestinationWf)
    have sourceValue := Val_ok.numtype s .I32 nextSource storeWf (val_wf_of_admin nextSourceWf)
    have countValue := Val_ok.numtype s .I32 nextCount storeWf (val_wf_of_admin nextCountWf)
    have recur := instruction_on_values storeWf originalInit (.cons destValue (.cons sourceValue (.cons countValue .nil)))
    have representation : admininstr_val (val_ref (fun_elem ⟨s,frame⟩ elementIndex).REFS[position]!) =
        admininstr_ref (fun_elem ⟨s,frame⟩ elementIndex).REFS[position]! := by
      cases (fun_elem ⟨s,frame⟩ elementIndex).REFS[position]! <;> rfl
    have combined := instrs_sequence first recur
    simp only [vals,List.map_cons,List.map_nil] at combined
    rw [representation] at combined
    simpa only [admininstr_val,admininstr_instr,List.append_assoc,List.cons_append,List.nil_append] using combined
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

end Exec.Spec
