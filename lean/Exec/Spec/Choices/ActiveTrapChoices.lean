import Exec.Spec.Choices.StepChoiceCoverage
import Exec.Spec.Choices.ChosenCounted
namespace Exec.Spec
open SpecExt

/-- Active cleanup consumes no policy-dependent reply, even when discarded
continuations contain choosing operators. -/
theorem ChoiceStep.repolicy_active {left right : SourceChoices} (leftValid : left.Admissible)
    {occurrence : Nat} {before after : config} {events : List HostEvent}
    (source : ChoiceStep left occurrence before events after) : activeTrap (trapCode before)=true →
      ChoiceStep right occurrence before events after := by
  induction source
  all_goals intro active
  case ordinary source free => exact .ordinary source free
  case ordinary_pure source free input output => exact .ordinary_pure source free input output
  case ordinary_read source input output => exact .ordinary_read source input output
  case ordinary_write source free => exact .ordinary_write source free
  case numeric =>
    casesm* NumericRequest
    all_goals simp [trapCode,NumericRequest.instructions,activeTrap] at active
  case vector =>
    casesm* VectorRequest
    all_goals simp [trapCode,VectorRequest.instructions,activeTrap] at active
  case memory => simp [trapCode,Segment.i32,activeTrap] at active
  case table =>
    casesm* ref
    all_goals simp [trapCode,Segment.i32,admininstr_ref,activeTrap] at active
  case host => simp [trapCode,activeTrap_vals,activeTrap] at active
  case label source input output ih =>
    apply ChoiceStep.label (ih ?_) input output
    simpa only [trapCode,activeTrap] using active
  case frame source input output ih =>
    apply ChoiceStep.frame (ih ?_) input output
    simpa only [trapCode,activeTrap] using active
  case instrs z z' front body body' tail events source nonempty input output ih =>
    apply ChoiceStep.instrs (ih ?_) nonempty input output
    have suffix := stepH_activeTrap_suffix (source.erases leftValid) tail
    dsimp only [trapCode] at active suffix
    rw [activeTrap_vals,suffix] at active
    exact active

theorem active_source_chosen (choices : SourceChoices) (occurrence : Nat) {before after : config} {events : List HostEvent}
    (source : StepH before events after) (active : activeTrap (trapCode before)=true) :
    ChoiceStep choices occurrence before events after := by
  obtain ⟨rfl,ordinary⟩ := stepH_active_ordinary source active
  obtain ⟨selected,valid,chosen⟩ := step_choices ordinary occurrence
  exact chosen.repolicy_active valid active

theorem StepsHN.active_chosen (choices : SourceChoices) {count : Nat} {before after : config} {events : List HostEvent}
    (source : StepsHN count before events after) (occurrence : Nat) (active : activeTrap (trapCode before)=true) :
    ChosenStepsN choices occurrence count before events after := by
  induction source generalizing occurrence with
  | refl wf => exact .refl occurrence wf
  | cons first tail ih =>
    exact .cons (active_source_chosen choices occurrence first active)
      (ih (occurrence+1) (stepH_active_trap first active).2.2.1)
end Exec.Spec
