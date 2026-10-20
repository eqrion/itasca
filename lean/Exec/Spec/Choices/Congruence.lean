import Exec.Spec.Choices.Infinite

/-! Occurrence-local congruence and coherent source policy composition. -/

namespace Exec.Spec

structure SourceChoices.AgreeAt (first second : SourceChoices) (occurrence : Nat) : Prop where
  host : first.host occurrence = second.host occurrence
  numeric : first.numeric occurrence = second.numeric occurrence
  vector : first.vector occurrence = second.vector occurrence
  memory : first.memory occurrence = second.memory occurrence
  table : first.table occurrence = second.table occurrence

theorem SourceChoices.AgreeAt.symm {first second : SourceChoices} {occurrence : Nat}
    (same : first.AgreeAt second occurrence) :
    second.AgreeAt first occurrence :=
  ⟨same.host.symm,same.numeric.symm,same.vector.symm,same.memory.symm,same.table.symm⟩

theorem ChosenNumeric.congr {first second : NumericChoices} {occurrence request result}
    (same : first occurrence = second occurrence) (source : ChosenNumeric first occurrence request result) :
    ChosenNumeric second occurrence request result := by
  cases source with
  | selected allowed source =>
    rw [same]
    exact .selected allowed source

theorem ChosenVector.congr {first second : VectorChoices} {occurrence request result}
    (same : first occurrence = second occurrence) (source : ChosenVector first occurrence request result) :
    ChosenVector second occurrence request result := by
  cases source with
  | selected allowed =>
    have fresh : second.AdmissibleAt occurrence request := by
      unfold VectorChoices.AdmissibleAt at *
      rw [←same]
      exact allowed
    simpa only [same] using ChosenVector.selected fresh

/-- A reduction consumes policies only at its own occurrence, through every
source evaluation context. -/
theorem ChoiceStep.congr {first second : SourceChoices} {occurrence before events after}
    (same : first.AgreeAt second occurrence) (source : ChoiceStep first occurrence before events after) :
    ChoiceStep second occurrence before events after := by
  induction source with
  | ordinary source free => exact .ordinary source free
  | ordinary_pure source free input output => exact .ordinary_pure source free input output
  | ordinary_read source input output => exact .ordinary_read source input output
  | ordinary_write source free => exact .ordinary_write source free
  | numeric chosen input output => exact .numeric (chosen.congr same.numeric) input output
  | vector chosen input output => exact .vector (chosen.congr same.vector) input output
  | memory s f delta storeWf frameWf deltaBound mapped bounded =>
    simpa only [same.memory] using ChoiceStep.memory (choices := second) (occurrence := occurrence)
      s f delta storeWf frameWf deltaBound (by simpa only [same.memory] using mapped)
      (by simpa only [same.memory] using bounded)
  | table s f index delta value storeWf frameWf indexBound deltaBound mapped bounded =>
    simpa only [same.table] using ChoiceStep.table (choices := second) (occurrence := occurrence)
      s f index delta value storeWf frameWf indexBound deltaBound (by simpa only [same.table] using mapped)
      (by simpa only [same.table] using bounded)
  | host s f address identity params results args typed frameWf host arguments =>
    simpa only [same.host] using ChoiceStep.host (choices := second) (occurrence := occurrence)
      s f address identity params results args typed frameWf host arguments
  | label _ input output ih => exact .label ih input output
  | frame _ input output ih => exact .frame ih input output
  | instrs _ nonempty input output ih => exact .instrs ih nonempty input output

/-- Stitch independently admissible occurrence policies into one fixed policy. -/
def SourceChoices.diagonal (policies : Nat → SourceChoices) : SourceChoices where
  host n := (policies n).host n
  numeric n := (policies n).numeric n
  vector n := (policies n).vector n
  memory n := (policies n).memory n
  table n := (policies n).table n

theorem SourceChoices.diagonal_admissible (policies : Nat → SourceChoices)
    (admissible : ∀ n, (policies n).Admissible) : (SourceChoices.diagonal policies).Admissible :=
  ⟨(fun n => (admissible n).host n),(fun n => (admissible n).numeric n),
    (fun n => (admissible n).vector n),(fun n => (admissible n).memory n),(fun n => (admissible n).table n)⟩

theorem SourceChoices.diagonal_agrees (policies : Nat → SourceChoices) (n : Nat) :
    (SourceChoices.diagonal policies).AgreeAt (policies n) n := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Every coherent stream of independently chosen source steps can use one
admissible fixed policy. This is source expressiveness, not interpreter matching. -/
theorem chosen_stream_policy (states : Nat → config) (events : Nat → List SpecExt.HostEvent)
    (covered : ∀ n, ∃ choices : SourceChoices, choices.Admissible ∧
      ChoiceStep choices n (states n) (events n) (states (n+1))) :
    ∃ choices : SourceChoices, choices.Admissible ∧ InfiniteChosenSource choices 0 (states 0) := by
  classical
  choose policies admissible edges using covered
  refine ⟨SourceChoices.diagonal policies,SourceChoices.diagonal_admissible policies admissible,
    states,events,rfl,?_⟩
  intro n
  simpa only [Nat.zero_add] using (edges n).congr (SourceChoices.diagonal_agrees policies n).symm

end Exec.Spec

