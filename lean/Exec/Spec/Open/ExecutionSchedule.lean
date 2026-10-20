import Exec.Spec.Open.ExecutionTraces
namespace Exec.Spec.OpenExecution

/-- A source schedule selects one independently permitted combined transition
at each occurrence. It may select Wasm, host control, API, or nesting progress;
it contains no equation about a concrete interpreter or callback computation. -/
structure Schedule (H : Type) where
  next : Nat → State H → Option (List Observation × State H)

def Schedule.Admissible {H : Type} (schedule : Schedule H) (model : HostModel H) : Prop:=
  ∀occurrence before events after,schedule.next occurrence before=some (events,after) →
    Transition model before events after

def ScheduledStep {H : Type} (schedule : Schedule H) (occurrence : Nat)
    (before : State H) (events : List Observation) (after : State H) : Prop:=
  schedule.next occurrence before=some (events,after)

theorem ScheduledStep.deterministic {H : Type} {schedule : Schedule H} {occurrence before events more after other}
    (first : ScheduledStep schedule occurrence before events after)
    (second : ScheduledStep schedule occurrence before more other) : events=more ∧ after=other := by
  exact Prod.mk.inj (Option.some.inj (first.symm.trans second))

inductive ScheduledTrace {H : Type} (schedule : Schedule H) : Nat → Nat → State H → List Observation → State H → Prop
  | nil (occurrence state) : ScheduledTrace schedule occurrence 0 state [] state
  | next {occurrence count first middle last events more}
      (step : ScheduledStep schedule occurrence first events middle)
      (tail : ScheduledTrace schedule (occurrence+1) count middle more last) :
      ScheduledTrace schedule occurrence (count+1) first (events++more) last

theorem ScheduledTrace.erases {H : Type} {schedule : Schedule H} {model : HostModel H}
    (admissible : schedule.Admissible model) {occurrence count first events last}
    (trace : ScheduledTrace schedule occurrence count first events last) : Trace model count first events last := by
  induction trace with
  | nil _ _=>exact .nil _
  | next step tail ih=>exact .next (admissible _ _ _ _ step) ih

theorem ScheduledTrace.trans {H : Type} {schedule : Schedule H} {occurrence count more first middle last events observed}
    (head : ScheduledTrace schedule occurrence count first events middle)
    (tail : ScheduledTrace schedule (occurrence+count) more middle observed last) :
    ScheduledTrace schedule occurrence (count+more) first (events++observed) last := by
  induction head with
  | nil occurrence state=>simpa only [Nat.add_zero,Nat.zero_add,List.nil_append] using tail
  | @next occurrence count first middle endpoint events more step rest ih=>
    have final:=ih (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc] using ScheduledTrace.next step final

def ScheduledInfinite {H : Type} (schedule : Schedule H) (occurrence : Nat) (first : State H) : Prop:=
  ∃states : Nat → State H,∃events : Nat → List Observation,states 0=first ∧
    ∀n,ScheduledStep schedule (occurrence+n) (states n) (events n) (states (n+1))

theorem ScheduledInfinite.erases {H : Type} {schedule : Schedule H} {model : HostModel H}
    (admissible : schedule.Admissible model) {occurrence first}
    (infinite : ScheduledInfinite schedule occurrence first) : InfiniteTrace model first := by
  obtain ⟨states,events,initial,steps⟩:=infinite
  exact ⟨states,events,initial,fun n=>admissible _ _ _ _ (steps n)⟩

theorem ScheduledInfinite.uncons {H : Type} {schedule : Schedule H} {occurrence first}
    (infinite : ScheduledInfinite schedule occurrence first) :
    ∃events middle,ScheduledStep schedule occurrence first events middle ∧ ScheduledInfinite schedule (occurrence+1) middle := by
  obtain ⟨states,events,initial,steps⟩:=infinite
  refine ⟨events 0,states 1,?_,fun n=>states (n+1),fun n=>events (n+1),rfl,?_⟩
  · simpa only [initial,Nat.add_zero] using steps 0
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using steps (n+1)

/-- Completed roots have no source successors, independently of the schedule. -/
theorem completed_no_transition {H : Type} {model : HostModel H} (s : _root_.store)
    (result : InvocationResult) (stack : List (Continuation H)) {events after} :
    ¬Transition model ⟨s,.completed result,stack⟩ events after := by
  intro step
  cases step

/-- A terminating run under one fixed source schedule excludes an infinite
run under that same schedule. No global determinism premise is used. -/
theorem ScheduledTrace.completed_no_infinite {H : Type} {schedule : Schedule H} {model : HostModel H}
    (admissible : schedule.Admissible model) {occurrence count first events last}
    (trace : ScheduledTrace schedule occurrence count first events last)
    (completed : ∃result,last.mode=.completed result) : ¬ScheduledInfinite schedule occurrence first := by
  induction trace with
  | nil occurrence state=>
    intro infinite
    obtain ⟨events,middle,step,rest⟩:=infinite.uncons
    obtain ⟨result,mode⟩:=completed
    have actual:=admissible _ _ _ _ step
    rcases state with ⟨s,control,stack⟩
    dsimp only at mode
    subst control
    exact completed_no_transition s result stack actual
  | next step tail ih=>
    intro infinite
    obtain ⟨events,middle,head,rest⟩:=infinite.uncons
    obtain ⟨same,rfl⟩:=step.deterministic head
    exact ih completed rest
end Exec.Spec.OpenExecution
