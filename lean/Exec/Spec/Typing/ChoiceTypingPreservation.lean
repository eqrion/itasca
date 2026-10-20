import Exec.Spec.Typing.HostStepPreservation
import Exec.Spec.Choices.StepChoiceCoverage
import Exec.Spec.Choices.Congruence

/-! Typing of chosen reductions and whole-run source choice coverage from one
typed entry. Policy existence is distinct from matching a concrete platform. -/
namespace Exec.Spec
open SpecExt

theorem ChoiceStep.config_preserved {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence before events after types} (source : ChoiceStep choices occurrence before events after)
    (typed : Config_ok before types) : Config_ok after types :=
  stepH_config_preserved (source.erases admissible) typed

theorem ChoiceSteps.config_preserved {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence before events after types} (source : ChoiceSteps choices occurrence before events after)
    (typed : Config_ok before types) : Config_ok after types :=
  stepsH_config_preserved (source.erases admissible) typed

theorem ChoiceSteps.congr_from {first second : SourceChoices} {occurrence before events after}
    (same : ∀ n, occurrence≤n → first.AgreeAt second n)
    (source : ChoiceSteps first occurrence before events after) : ChoiceSteps second occurrence before events after := by
  induction source with
  | refl occurrence wf => exact .refl occurrence wf
  | @cons occurrence before middle after events rest first tail ih =>
    exact .cons (first.congr (same occurrence (by omega))) (ih (fun n bound => same n (by omega)))

/-- A single fixed admissible policy represents the entire finite typed source
run, including intermediate host effects. No intermediate typing is assumed. -/
theorem typed_run_choices {before events after types} (source : StepsH before events after)
    (typed : Config_ok before types) (occurrence : Nat) :
    ∃ choices : SourceChoices, choices.Admissible ∧ ChoiceSteps choices occurrence before events after := by
  classical
  induction source generalizing occurrence with
  | refl wf => exact ⟨defaultSourceChoices,defaultSourceChoices_admissible,.refl occurrence wf⟩
  | @cons before middle after events rest first tail ih =>
    obtain ⟨head,headValid,headStep⟩ := typed_step_choices first typed occurrence
    obtain ⟨remaining,remainingValid,remainingSteps⟩ := ih (stepH_config_preserved first typed) (occurrence+1)
    let policies (n : Nat) : SourceChoices := if n=occurrence then head else remaining
    let choices := SourceChoices.diagonal policies
    have valid : choices.Admissible := SourceChoices.diagonal_admissible policies (by
      intro n
      dsimp [policies]
      split <;> assumption)
    have headAgree : head.AgreeAt choices occurrence := by
      have same := SourceChoices.diagonal_agrees policies occurrence
      simpa only [policies,if_pos rfl] using same.symm
    have tailAgree : ∀ n, occurrence+1≤n → remaining.AgreeAt choices n := by
      intro n bound
      have same := SourceChoices.diagonal_agrees policies n
      simpa only [policies,if_neg (by omega : n≠occurrence)] using same.symm
    exact ⟨choices,valid,.cons (headStep.congr headAgree) (remainingSteps.congr_from tailAgree)⟩

/-- Source preservation supplies typing at every point of an infinite
one-step stream, so its policy coverage needs only initial typing. -/
theorem typed_stream_choices (states : Nat → config) (events : Nat → List HostEvent) {types}
    (typed : Config_ok (states 0) types)
    (edges : ∀ n, StepH (states n) (events n) (states (n+1))) :
    ∃ choices : SourceChoices, choices.Admissible ∧ InfiniteChosenSource choices 0 (states 0) := by
  have every : ∀ n, Config_ok (states n) types := by
    intro n
    induction n with
    | zero => exact typed
    | succ n ih => exact stepH_config_preserved (edges n) ih
  exact chosen_stream_policy states events (fun n => typed_step_choices (edges n) (every n) n)

/-- Expose one real reduction from an infinite positive-chunk run. The
remaining finite chunk is retained as a prefix of the infinite tail. -/
theorem InfiniteSourceWithEvents.uncons {initial : config} (source : InfiniteSourceWithEvents initial) :
    ∃ events next, StepH initial events next ∧ InfiniteSourceWithEvents next := by
  obtain ⟨states,events,first,edges⟩ := source
  have remaining : InfiniteSourceWithEvents (states 1) :=
    ⟨(fun n => states (n+1)),(fun n => events (n+1)),rfl,(fun n => by simpa [Nat.add_assoc] using edges (n+1))⟩
  obtain ⟨count,positive,chunk⟩ := edges 0
  rw [first] at chunk
  generalize eventEq : events 0=firstEvents at chunk
  generalize finalEq : states (0+1)=final at chunk
  cases chunk with
  | refl => omega
  | cons head tail =>
    have suffix : InfiniteSourceWithEvents final := by simpa only [← finalEq] using remaining
    exact ⟨_,_,head,suffix.prepend tail.erase⟩

/-- Every infinite strengthened source run from a typed entry has an
infinite execution under one fixed independently admissible policy. This
existential result does not identify a concrete platform's policy. -/
theorem typed_infinite_choices {initial : config} {types : resulttype}
    (typed : Config_ok initial types) (source : InfiniteSourceWithEvents initial) :
    ∃ choices : SourceChoices, choices.Admissible ∧ InfiniteChosenSource choices 0 initial := by
  classical
  let Running := {c : config // InfiniteSourceWithEvents c}
  have advance : ∀ current : Running, ∃ events next,
      StepH current.val events next ∧ InfiniteSourceWithEvents next := fun current => current.property.uncons
  choose events next edge remaining using advance
  let successor (current : Running) : Running := ⟨next current,remaining current⟩
  let states : Nat → Running := fun n => Nat.rec ⟨initial,source⟩ (fun _ previous => successor previous) n
  have edges : ∀ n, StepH (states n).val (events (states n)) (states (n+1)).val := fun n => edge (states n)
  exact typed_stream_choices (fun n => (states n).val) (fun n => events (states n)) typed edges

end Exec.Spec
