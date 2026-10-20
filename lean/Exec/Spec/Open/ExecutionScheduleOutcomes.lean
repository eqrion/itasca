import Exec.Spec.Open.ExecutionSchedule
namespace Exec.Spec.OpenExecution

theorem completed_state_no_transition {H : Type} {model : HostModel H} {state : State H}
    (completed : ∃result,state.mode=.completed result) {events after} : ¬Transition model state events after := by
  obtain ⟨result,mode⟩:=completed
  rcases state with ⟨s,control,stack⟩
  dsimp only at mode
  subst control
  exact completed_no_transition s result stack

/-- Two completed source runs under the same occurrence-indexed schedule have
identical results, stores and expanded observations, with the same length. -/
theorem ScheduledTrace.completed_unique {H : Type} {schedule : Schedule H} {model : HostModel H}
    (admissible : schedule.Admissible model) {occurrence count first events last}
    (trace : ScheduledTrace schedule occurrence count first events last)
    (completed : ∃result,last.mode=.completed result)
    {otherCount more endpoint} (other : ScheduledTrace schedule occurrence otherCount first more endpoint)
    (otherCompleted : ∃result,endpoint.mode=.completed result) :
    count=otherCount ∧ events=more ∧ last=endpoint := by
  induction trace generalizing otherCount more endpoint with
  | nil occurrence state=>
    cases other with
    | nil=>exact ⟨rfl,rfl,rfl⟩
    | next step rest=>exact False.elim (completed_state_no_transition completed (admissible _ _ _ _ step))
  | next step tail ih=>
    cases other with
    | nil=>exact False.elim (completed_state_no_transition otherCompleted (admissible _ _ _ _ step))
    | next head rest=>
      obtain ⟨rfl,rfl⟩:=step.deterministic head
      obtain ⟨rfl,rfl,rfl⟩:=ih completed rest otherCompleted
      exact ⟨rfl,rfl,rfl⟩
end Exec.Spec.OpenExecution
