import Exec.Abs.Executable.ChosenStep
import Exec.Abs.Executable.Run
import Exec.Spec.Choices.ChosenProgress
namespace Exec.Abs.Executable
open SpecExt Exec.Spec

/-- A local proof produces the reduction count; the run never assumes a source
trace or its final outcome as a compatibility premise. -/
noncomputable def ChosenStep.cost {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before next}
    (step : ChosenStep choices occurrence before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) : Nat :=
  if silent : decode before=decode next ∧ administrativeMeasure next<administrativeMeasure before then 0
  else Classical.choose ((step.next_simulation admissible vector typed covered).resolve_left silent)

theorem ChosenStep.cost_spec {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before next}
    (step : ChosenStep choices occurrence before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) :
    ChosenStepsN choices occurrence (step.cost admissible vector typed covered) (decode before) [] (decode next) ∧
      (step.cost admissible vector typed covered=0 → administrativeMeasure next<administrativeMeasure before) := by
  classical
  unfold ChosenStep.cost
  split
  · rename_i silent
    exact ⟨silent.1 ▸ ChosenStepsN.refl occurrence typed.typed.decode_wf,fun _ => silent.2⟩
  · rename_i active
    obtain ⟨positive,source⟩ := Classical.choose_spec ((step.next_simulation admissible vector typed covered).resolve_left active)
    exact ⟨source,fun zero => by omega⟩

structure ChosenPoint where
  state : AState
  occurrence : Nat
  typed : CoreTyped state
  covered : ExecutableState state

/-- Only primitive chosen steps and their proved local reduction count enter
the clock. There is no assumed source history in this relation. -/
inductive ChosenEdge (choices : SourceChoices) (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (before after : ChosenPoint) : Prop where
  | next (step : ChosenStep choices before.occurrence before.state (.next after.state))
      (clock : after.occurrence=before.occurrence+step.cost admissible vector before.typed before.covered)

theorem ChosenEdge.erases {choices admissible vector before after}
    (edge : ChosenEdge choices admissible vector before after) : Step before.state (.next after.state) := by
  cases edge with | next step clock => exact step.erases admissible

theorem ChosenEdge.simulation {choices admissible vector before after}
    (edge : ChosenEdge choices admissible vector before after) :
    ChosenDispatchSim choices (fun p : ChosenPoint=>decode p.state) ChosenPoint.occurrence
      (fun p=>administrativeMeasure p.state) before [] after := by
  cases edge with
  | next step clock =>
    obtain ⟨source,decrease⟩ := step.cost_spec admissible vector before.typed before.covered
    by_cases zero : step.cost admissible vector before.typed before.covered=0
    · exact .inl ⟨(zero ▸ source).zero.1,by simpa only [zero,Nat.add_zero] using clock,rfl,decrease zero⟩
    · exact .inr ⟨_,Nat.pos_of_ne_zero zero,clock,source⟩

inductive ChosenRun (choices : SourceChoices) (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) : Nat → ChosenPoint → ChosenPoint → Prop where
  | refl (state : ChosenPoint) : ChosenRun choices admissible vector 0 state state
  | next {before middle last n} (step : ChosenEdge choices admissible vector before middle)
      (tail : ChosenRun choices admissible vector n middle last) : ChosenRun choices admissible vector (n+1) before last

theorem ChosenRun.erases {choices admissible vector n before after}
    (run : ChosenRun choices admissible vector n before after) : Run n before.state after.state := by
  induction run with
  | refl state => exact .refl _
  | next step tail ih => exact .next step.erases ih

theorem ChosenRun.source {choices admissible vector n before after}
    (run : ChosenRun choices admissible vector n before after) :
    ∃ count, after.occurrence=before.occurrence+count ∧
      ChosenStepsN choices before.occurrence count (decode before.state) [] (decode after.state) := by
  induction run with
  | refl point => exact ⟨0,(Nat.add_zero _).symm,.refl _ point.typed.typed.decode_wf⟩
  | @next before middle last n edge tail ih =>
    cases edge with
    | next step clock =>
      obtain ⟨count,finalClock,rest⟩ := ih
      have source := (step.cost_spec admissible vector before.typed before.covered).1
      rw [clock] at rest finalClock
      exact ⟨_,by simpa only [Nat.add_assoc] using finalClock,by simpa only [List.nil_append] using source.trans rest⟩

theorem ChosenRun.done {choices admissible vector n before after values}
    (run : ChosenRun choices admissible vector n before after)
    (done : ChosenStep choices after.occurrence after.state (.done values)) :
    ∃ count, ChosenStepsN choices before.occurrence count (decode before.state) []
      ⟨⟨after.state.store,after.state.ambient⟩,vals values⟩ := by
  obtain ⟨count,_,source⟩ := run.source
  exact ⟨count,(done.erases admissible).done_simulation after.typed ▸ source⟩

theorem ChosenRun.trap {choices admissible vector n before after}
    (run : ChosenRun choices admissible vector n before after)
    (trap : ChosenStep choices after.occurrence after.state .trap) :
    ∃ count,0<count ∧ ChosenStepsN choices before.occurrence count (decode before.state) []
      ⟨⟨after.state.store,after.state.ambient⟩,[.TRAP]⟩ := by
  obtain ⟨count,clock,source⟩ := run.source
  obtain ⟨suffix,positive,trapped⟩ := trap.trap_simulation admissible vector after.typed after.covered
  rw [clock] at trapped
  exact ⟨count+suffix,by omega,by simpa only [List.nil_append] using source.trans trapped⟩

/-- Any productive full-language abstract execution with these primitive
choices reflects an infinite source run under exactly the same policy. -/
theorem chosen_execution_infinite {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (running : ChosenPoint → Prop)
    (advance : ∀ before, running before → ∃ after, ChosenEdge choices admissible vector before after ∧ running after)
    (initial : ChosenPoint) (active : running initial) :
    InfiniteChosenSource choices initial.occurrence (decode initial.state) := by
  let State := {point : ChosenPoint // running point}
  let edge := fun (before : State) (events : List HostEvent) (after : State) =>
    events=[] ∧ ChosenEdge choices admissible vector before.val after.val
  apply infinite_chosen_of_decreasing_stutter choices edge (fun p=>decode p.val.state)
    (fun p=>p.val.occurrence) (fun p=>administrativeMeasure p.val.state) ?_ ?_ ⟨initial,active⟩
  · intro before
    obtain ⟨after,step,held⟩ := advance before.val before.property
    exact ⟨[],⟨after,held⟩,rfl,step⟩
  · rintro before events after ⟨rfl,step⟩
    exact step.simulation
end Exec.Abs.Executable
