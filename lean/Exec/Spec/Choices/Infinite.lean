import Exec.Spec.Choices.Steps
import Exec.Spec.EventfulInfinite

namespace Exec.Spec
open SpecExt

/-- A coherent infinite run under one fixed policy, retaining the occurrence
and direct events at every reduction. This is stronger evidence than an
unindexed existential source divergence. -/
def InfiniteChosenSource (choices : SourceChoices) (occurrence : Nat) (initial : config) : Prop :=
  ∃ states : Nat → config, ∃ events : Nat → List HostEvent,
    states 0 = initial ∧ ∀ n,
      ChoiceStep choices (occurrence + n) (states n) (events n) (states (n+1))

/-- Forgetting policies preserves every state and event of the infinite run. -/
theorem InfiniteChosenSource.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence initial} (infinite : InfiniteChosenSource choices occurrence initial) :
    InfiniteSourceWithEvents initial := by
  obtain ⟨states,events,first,edges⟩ := infinite
  refine ⟨states,events,first,?_⟩
  intro n
  have edge := (edges n).erases admissible
  exact ⟨1,by decide,by simpa using StepsHN.cons edge (StepsHN.refl (stepH_wf edge).2)⟩

end Exec.Spec
