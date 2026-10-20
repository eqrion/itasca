import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

private theorem selected_action_not_invoke (choices : SourceOperationChoices) (occurrence : Nat)
    (s : store) (control next : SourceControl) (t : store) (address : funcaddr) (args : List val) (caller : SourceControl)
    (action : chosenSourceAction choices occurrence s control=some (t,next))
    (invoke : chosenSourceInvoke occurrence control=some (address,args,caller)) : ¬address<s.FUNCS.length := by
  cases control with
  | draft result => cases invoke
  | active h =>
    cases selected : h.code[h.pc]? with
    | none => simp only [chosenSourceInvoke,selected] at invoke; cases invoke
    | some instruction =>
      cases instruction <;> simp only [chosenSourceInvoke,selected] at invoke
      all_goals cases invoke
      rename_i index values nextPC
      intro bound
      simp only [chosenSourceAction,selected,if_pos bound] at action
      cases action

private theorem selected_finish_draft {control : SourceControl} {result : Option (List val)}
    (finished : (match control with | .draft proposed => some proposed | .active _ => none)=some result) : control=.draft result := by
  cases control with
  | active h => cases finished
  | draft proposed => cases Option.some.inj finished; rfl

/-- Outside Wasm reduction and host entry, the immutable callback choices
select one exact next combined state and observation. -/
theorem control_choice_deterministic {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    (select : Selector) (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) {occurrence first leftEvents rightEvents left right}
    (firstStep : Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence first leftEvents left)
    (secondStep : Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence first rightEvents right)
    (outside : ∀f body expected,first.mode≠.wasm f body expected) : leftEvents=rightEvents ∧ left=right := by
  cases firstStep with
  | wasm edge => exact False.elim (outside _ _ _ rfl)
  | enter suspended same atStore expectedEq => exact False.elim (outside _ _ _ rfl)
  | values => exact False.elim (outside _ _ _ rfl)
  | trap => exact False.elim (outside _ _ _ rfl)
  | action selected =>
    cases secondStep with
    | action other =>
      have eq:=Option.some.inj (selected.symm.trans other)
      cases eq
      exact ⟨rfl,rfl⟩
    | requestInvoke invoked bound signature => exact False.elim (selected_action_not_invoke choices _ _ _ _ _ _ _ _ selected invoked bound)
    | finish finished =>
      have draft:=selected_finish_draft (control := _) (result := _) (by exact finished)
      rw [draft] at selected
      cases selected
  | requestInvoke selected bound signature =>
    cases secondStep with
    | action other => exact False.elim (selected_action_not_invoke choices _ _ _ _ _ _ _ _ other selected bound)
    | requestInvoke other otherBound otherSignature =>
      have eq:=Option.some.inj (selected.symm.trans other)
      cases eq
      have types:=signature.symm.trans otherSignature
      cases types
      exact ⟨rfl,rfl⟩
    | finish finished =>
      have draft:=selected_finish_draft (control := _) (result := _) (by exact finished)
      rw [draft] at selected
      cases selected
  | finish selected =>
    cases secondStep with
    | finish other => cases Option.some.inj (selected.symm.trans other);exact ⟨rfl,rfl⟩
    | action other =>
      have draft:=selected_finish_draft (control := _) (result := _) (by exact selected)
      rw [draft] at other
      cases other
    | requestInvoke other bound signature =>
      have draft:=selected_finish_draft (control := _) (result := _) (by exact selected)
      rw [draft] at other
      cases other
  | acceptInvoke typed =>
    cases secondStep with
    | acceptInvoke other => exact ⟨rfl,rfl⟩
    | rejectInvoke rejected => exact False.elim (rejected typed)
  | rejectInvoke rejected =>
    cases secondStep with
    | acceptInvoke typed => exact False.elim (rejected typed)
    | rejectInvoke other => exact ⟨rfl,rfl⟩
  | resumeHost => cases secondStep;exact ⟨rfl,rfl⟩
  | completeInvoke => cases secondStep;exact ⟨rfl,rfl⟩
  | resumeWasm reply completed =>
    cases secondStep with
    | resumeWasm other otherCompleted =>
      cases completed.symm.trans otherCompleted
      exact ⟨rfl,rfl⟩
    | rejectWasm rejected other otherCompleted => exact False.elim (rejected (reply.2.2 _ rfl))
  | rejectWasm rejected reply completed =>
    cases secondStep with
    | resumeWasm other otherCompleted => exact False.elim (rejected (other.2.2 _ rfl))
    | rejectWasm otherRejected other otherCompleted =>
      cases completed.symm.trans otherCompleted
      exact ⟨rfl,rfl⟩
end Exec.Theorems.OpenReentrantControl
