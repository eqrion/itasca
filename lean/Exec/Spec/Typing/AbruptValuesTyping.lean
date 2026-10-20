import Exec.Spec.Typing.ValueOperationTyping

/-! Value suffix typing and preservation for early return and branch unwinding.
The generated label/frame arities determine which actual values survive. -/

namespace Exec.Spec
open SpecExt

theorem resultsTyped_suffix {s : store} {front returned : List val} {base types : List valtype}
    (typed : ResultsTyped s (base++types) (front++returned)) (count : returned.length=types.length) :
    ResultsTyped s types returned := by
  change List.Forall₂ (Val_ok s) returned types
  have allCount := typed.length_eq
  have frontCount : front.length=base.length := by simp only [List.length_append] at allCount; omega
  have selected := List.forall₂_drop front.length typed
  simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at selected
  simpa only [frontCount,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] using selected

theorem abrupt_values_typed {s : store} {context : _root_.context} {front returned : List val}
    {op : admininstr} {tail : List admininstr} {output types : List valtype}
    (typed : Instrs_ok2 s context (vals (front++returned)++([op]++tail))
      (.mk_functype (.mk_list []) (.mk_list output)))
    (arity : returned.length=types.length)
    (operation : ∀ params results,
      Instr_ok2 s context op (.mk_functype (.mk_list params) (.mk_list results)) →
      ∃ discarded, params=discarded++types) : ResultsTyped s types returned := by
  obtain ⟨actual,arguments,rest⟩ := closed_value_prefix_typing typed
  obtain ⟨middle,called,_⟩ := instrs_typing_split rest [op] tail rfl
  obtain ⟨base,params,results,primitive,inputSub,_⟩ := instruction_typing_effect called op rfl
  obtain ⟨discarded,rfl⟩ := operation params results primitive
  have argumentTypes : ResultsTyped s ((base++discarded)++types) (front++returned) := by
    simpa only [List.append_assoc] using resultsTyped_subtype arguments inputSub
  exact resultsTyped_suffix argumentTypes arity

theorem return_input_shape {s : store} {context : _root_.context} {instruction : admininstr}
    {input output types : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.RETURN) (returns : context.RETURN=some (.mk_list types)) :
    ∃ discarded, input=discarded++types := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases primitive
    rename_i discarded actual _ _ _
    have actualReturn : context.RETURN=some (.mk_list actual) := by assumption
    have sameTypes : actual=types := by simpa only [returns,Option.some.injEq,list.mk_list.injEq] using actualReturn.symm
    subst actual
    exact ⟨discarded,rfl⟩
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem return_frame_typing_preserved (s : store) (arity : Nat) (frame : _root_.frame)
    (front returned : List val) (tail : List admininstr) (count : arity=returned.length) :
    TypedReplacement s s [.FRAME_ arity frame (vals (front++returned)++([.RETURN]++tail))] (vals returned) := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.FRAME_ arity frame (vals (front++returned)++([.RETURN]++tail)) = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case Instr_ok2_frame =>
    cases same
    rename_i innerContext _ _ _ _ _ _ _ _
    let returnContext : _root_.context :=
      {(default : _root_.context) with RETURN := some (.mk_list output)} ++ innerContext
    have expression : Expr_ok2 s returnContext (vals (front++returned)++([.RETURN]++tail)) (.mk_list output) := by assumption
    have arityTyped : arity=output.length := by assumption
    have body : Instrs_ok2 s returnContext (vals (front++returned)++([.RETURN]++tail))
        (.mk_functype (.mk_list []) (.mk_list output)) := by
      cases expression
      assumption
    apply values_instrs_ok storeWf contextWf
    apply abrupt_values_typed body (count.symm.trans arityTyped)
    intro params results primitive
    exact return_input_shape primitive rfl rfl
  all_goals cases same

theorem branch_input_shape {s : store} {context : _root_.context} {instruction : admininstr}
    {input output types : List valtype} (index : labelidx)
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (same : instruction=.BR index) (selected : proj_list_0 valtype context.LABELS[proj_uN_0 index]! =types) :
    ∃ discarded, input=discarded++types := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i discarded actual _ _ _ _
    have actualTarget : proj_list_0 valtype context.LABELS[proj_uN_0 index]! =actual := by assumption
    have sameTypes : actual=types := actualTarget.symm.trans selected
    exact ⟨discarded,congrArg (fun types => discarded++types) sameTypes⟩
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem br_zero_typing_preserved (s : store) (arity : Nat) (cont : List instr)
    (front returned : List val) (tail : List admininstr) (count : arity=returned.length) :
    TypedReplacement s s [.LABEL_ arity cont (vals (front++returned)++([.BR (.mk_uN 0)]++tail))]
      (vals returned++cont.map admininstr_instr) := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.LABEL_ arity cont (vals (front++returned)++([.BR (.mk_uN 0)]++tail)) = instruction at typed
  have storeWf : wf_store s := by cases typed <;> assumption
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case label =>
    cases same
    rename_i branchTypes _ _ _ _ _ _ _
    let labelContext : _root_.context :=
      {(default : _root_.context) with LABELS := [.mk_list branchTypes]} ++ context
    have body : Instrs_ok2 s labelContext (vals (front++returned)++([.BR (.mk_uN 0)]++tail))
        (.mk_functype (.mk_list []) (.mk_list output)) := by assumption
    have arityTyped : arity=branchTypes.length := by assumption
    have values : ResultsTyped s branchTypes returned := by
      apply abrupt_values_typed body (count.symm.trans arityTyped)
      intro params results primitive
      exact branch_input_shape (.mk_uN 0) primitive rfl rfl
    have continuation : Instrs_ok2 s context (cont.map admininstr_instr)
        (.mk_functype (.mk_list branchTypes) (.mk_list output)) := by assumption
    exact instrs_sequence (values_instrs_ok storeWf contextWf values) continuation
  all_goals cases same

theorem instruction_typing_wf {s : store} {context : _root_.context} {instruction : admininstr} {type : functype}
    (typed : Instr_ok2 s context instruction type) : wf_admininstr instruction := by
  cases typed
  case ref =>
    rename_i reference type _ _ _
    have valid : Ref_ok s reference type := by assumption
    have storeWf : wf_store s := by assumption
    have same : admininstr_val (val_ref reference)=admininstr_ref reference := by cases reference <;> rfl
    rw [← same]
    exact wf_admininstr_val (val_ok_wf (.reftype _ _ _ valid storeWf))
  all_goals first
    | assumption
    | (apply wf_admininstr_instr; assumption)

theorem abrupt_prefix_typing {s : store} {oldContext newContext : _root_.context}
    {values : List val} {oldOp newOp : admininstr} {tail : List admininstr} {oldOutput output : List valtype}
    (typed : Instrs_ok2 s oldContext (vals values++([oldOp]++tail))
      (.mk_functype (.mk_list []) (.mk_list oldOutput)))
    (contextWf : wf_context newContext)
    (operation : ∀ params results,
      Instr_ok2 s oldContext oldOp (.mk_functype (.mk_list params) (.mk_list results)) →
      ∀ base target, Instr_ok2 s newContext newOp
        (.mk_functype (.mk_list (base++params)) (.mk_list target))) :
    Instrs_ok2 s newContext (vals values++[newOp]) (.mk_functype (.mk_list []) (.mk_list output)) := by
  obtain ⟨actual,arguments,rest⟩ := closed_value_prefix_typing typed
  obtain ⟨middle,called,_⟩ := instrs_typing_split rest [oldOp] tail rfl
  obtain ⟨base,params,results,primitive,inputSub,_⟩ := instruction_typing_effect called oldOp rfl
  have updated := operation params results primitive base output
  have storeWf := (instrs_ok2_wf typed).1
  have updatedWf := instruction_typing_wf updated
  have instruction := Instrs_ok2.instr _ _ _ _ _ updated storeWf contextWf updatedWf
  exact instrs_sequence (values_instrs_ok storeWf contextWf arguments)
    (instrs_subtype instruction inputSub (resulttype_sub_refl output))

theorem return_retarget {s : store} {oldContext newContext : _root_.context}
    {instruction : admininstr} {params results : List valtype}
    (typed : Instr_ok2 s oldContext instruction (.mk_functype (.mk_list params) (.mk_list results)))
    (same : instruction=.RETURN) (contextWf : wf_context newContext)
    (returns : newContext.RETURN=oldContext.RETURN) (base output : List valtype) :
    Instr_ok2 s newContext .RETURN (.mk_functype (.mk_list (base++params)) (.mk_list output)) := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have storeWf : wf_store s := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases primitive
    rename_i discarded actual _ _ _
    have actualReturn : oldContext.RETURN=some (.mk_list actual) := by assumption
    have updated := Instr_ok.return newContext (base++discarded) actual output
      (returns.trans actualReturn) contextWf .instr_case_12
    simpa only [List.append_assoc,admininstr_instr] using Instr_ok2.plain s newContext .RETURN
      ((base++discarded)++actual) output updated storeWf contextWf .instr_case_12
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem return_label_typing_preserved (s : store) (arity : Nat) (cont : List instr)
    (values : List val) (tail : List admininstr) :
    TypedReplacement s s [.LABEL_ arity cont (vals values++([.RETURN]++tail))] (vals values++[.RETURN]) := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.LABEL_ arity cont (vals values++([.RETURN]++tail)) = instruction at typed
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case label =>
    cases same
    rename_i branchTypes _ _ _ _ _ _ _
    let labelContext : _root_.context :=
      {(default : _root_.context) with LABELS := [.mk_list branchTypes]} ++ context
    have body : Instrs_ok2 s labelContext (vals values++([.RETURN]++tail))
        (.mk_functype (.mk_list []) (.mk_list output)) := by assumption
    apply abrupt_prefix_typing body contextWf
    intro params results primitive base target
    exact return_retarget primitive rfl contextWf rfl base target
  all_goals cases same

theorem branch_succ_retarget {s : store} {context : _root_.context} (branchTypes : List valtype)
    {instruction : admininstr} {params results : List valtype} (index : labelidx)
    (typed : Instr_ok2 s
      ({(default : _root_.context) with LABELS := [.mk_list branchTypes]} ++ context)
      instruction (.mk_functype (.mk_list params) (.mk_list results)))
    (same : instruction=.BR (.mk_uN (proj_uN_0 index+1))) (contextWf : wf_context context)
    (branchWf : wf_instr (.BR index)) (base output : List valtype) :
    Instr_ok2 s context (.BR index) (.mk_functype (.mk_list (base++params)) (.mk_list output)) := by
  cases typed
  case plain =>
    rename_i source _ _ _ primitive
    have storeWf : wf_store s := by assumption
    cases source <;> simp [admininstr_instr] at same
    cases same
    cases primitive
    rename_i discarded actual _ _ _ _
    have oldBound : proj_uN_0 index+1 < (.mk_list branchTypes::context.LABELS).length := by assumption
    have bound : proj_uN_0 index < context.LABELS.length := by simp only [List.length_cons] at oldBound; omega
    have oldType : proj_list_0 valtype (.mk_list branchTypes::context.LABELS)[proj_uN_0 index+1]! = actual := by assumption
    have found : proj_list_0 valtype context.LABELS[proj_uN_0 index]! = actual := by
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_cons_succ] using oldType
    have updated := Instr_ok.br context index (base++discarded) actual output bound found contextWf branchWf
    simpa only [List.append_assoc,admininstr_instr] using Instr_ok2.plain s context (.BR index)
      ((base++discarded)++actual) output updated storeWf contextWf branchWf
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  all_goals cases same

theorem br_succ_typing_preserved (s : store) (arity : Nat) (cont : List instr)
    (values : List val) (index : labelidx) (tail : List admininstr) (branchWf : wf_instr (.BR index)) :
    TypedReplacement s s [.LABEL_ arity cont (vals values++([.BR (.mk_uN (proj_uN_0 index+1))]++tail))]
      (vals values++[.BR index]) := by
  apply singleton_typing_replacement
  intro context input output typed
  generalize same : admininstr.LABEL_ arity cont
    (vals values++([.BR (.mk_uN (proj_uN_0 index+1))]++tail)) = instruction at typed
  have contextWf : wf_context context := by cases typed <;> assumption
  cases typed
  case plain =>
    rename_i source _ _ _ _
    cases source <;> simp [admininstr_instr] at same
  case ref =>
    rename_i reference _ _ _ _
    cases reference <;> simp [admininstr_ref] at same
  case label =>
    cases same
    rename_i branchTypes _ _ _ _ _ _ _
    let labelContext : _root_.context :=
      {(default : _root_.context) with LABELS := [.mk_list branchTypes]} ++ context
    have body : Instrs_ok2 s labelContext
        (vals values++([.BR (.mk_uN (proj_uN_0 index+1))]++tail))
        (.mk_functype (.mk_list []) (.mk_list output)) := by assumption
    apply abrupt_prefix_typing body contextWf
    intro params results primitive base target
    exact branch_succ_retarget branchTypes index primitive rfl contextWf branchWf base target
  all_goals cases same

end Exec.Spec
