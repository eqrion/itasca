import Exec.Spec.Open.HostChosen
import Exec.Spec.Choices.ChosenCounted
namespace Exec.Spec.OpenHost
open SpecExt

/-- An issued host request cannot be passed by a silent Wasm reduction. Host
control must enter through the combined machine's suspension transition. -/
theorem Pending.no_quiet_step {choices : SourceChoices} (allowed : choices.Admissible)
    (occurrence : Nat) (pending : Pending) (typed : Store_ok pending.before) {after : config} :
    ¬ChoiceStep choices occurrence pending.initial [] after := by
  intro quiet
  have host := pending.compress_chosen allowed occurrence typed
    (choices.host occurrence pending.before pending.address pending.identity pending.params pending.results pending.arguments) rfl
  have impossible := (choice_step_nonactive_deterministic allowed host quiet (pending.initial_nonactive typed)).1
  cases impossible

/-- Boundaries delimit one silent Wasm segment of open execution. Reaching a
host request does not assume that its eventual callback returns. -/
inductive QuietBoundary : config → Prop
  | terminal {configuration} (finished : SourceTerminal configuration) : QuietBoundary configuration
  | host (pending : Pending) (typed : Store_ok pending.before) : QuietBoundary pending.initial

theorem QuietBoundary.no_step {choices : SourceChoices} (allowed : choices.Admissible)
    {configuration : config} (boundary : QuietBoundary configuration) (occurrence : Nat) {after} :
    ¬ChoiceStep choices occurrence configuration [] after := by
  cases boundary with
  | terminal finished => exact fun step=>finished.no_step _ _ (step.erases allowed)
  | host pending typed => exact pending.no_quiet_step allowed occurrence typed

theorem QuietBoundary.active_outcome {choices : SourceChoices} (allowed : choices.Admissible)
    {occurrence count before after} (run : ChosenStepsN choices occurrence count before [] after)
    (active : activeTrap (trapCode before)=true) (boundary : QuietBoundary after) :
    after=⟨trapState before,[.TRAP]⟩ := by
  cases boundary with
  | terminal finished => exact (active_terminal_run active (run.erase_count.erases allowed) finished).2
  | host pending typed =>
    have activeAfter := ((run.erases allowed).active_trap active).2.2.1
    rw [pending.initial_nonactive typed] at activeAfter
    contradiction

/-- Two silent segments under the same primitive choices reach the same
boundary. Administrative trap cleanup may have different lengths. -/
theorem quiet_boundary_unique {choices : SourceChoices} (allowed : choices.Admissible)
    {occurrence count before after} (left : ChosenStepsN choices occurrence count before [] after)
    (leftBoundary : QuietBoundary after) {otherCount otherAfter}
    (right : ChosenStepsN choices occurrence otherCount before [] otherAfter)
    (rightBoundary : QuietBoundary otherAfter) : after=otherAfter := by
  generalize empty : ([] : List HostEvent)=events at left
  induction left generalizing otherCount otherAfter with
  | refl occurrence wf =>
    generalize rightEmpty : ([] : List HostEvent)=rightEvents at right
    cases right with
    | refl => rfl
    | cons head tail =>
      obtain ⟨rfl,rfl⟩:=List.append_eq_nil_iff.mp rightEmpty.symm
      exact False.elim (leftBoundary.no_step allowed occurrence head)
  | @cons occurrence count before middle after headEvents restEvents head tail ih =>
    obtain ⟨rfl,rfl⟩:=List.append_eq_nil_iff.mp empty.symm
    cases active : activeTrap (trapCode before) with
    | true =>
      have full : ChosenStepsN choices occurrence (count+1) before [] after := by
        simpa only [List.nil_append] using ChosenStepsN.cons head tail
      exact (leftBoundary.active_outcome allowed full active).trans
        (rightBoundary.active_outcome allowed right active).symm
    | false =>
      generalize rightEmpty : ([] : List HostEvent)=rightEvents at right
      cases right with
      | refl => exact False.elim (rightBoundary.no_step allowed occurrence head)
      | cons otherHead otherTail =>
        obtain ⟨rfl,rfl⟩:=List.append_eq_nil_iff.mp rightEmpty.symm
        obtain ⟨_,same⟩:=choice_step_nonactive_deterministic allowed head otherHead active
        cases same
        exact ih leftBoundary otherTail rightBoundary rfl
end Exec.Spec.OpenHost
