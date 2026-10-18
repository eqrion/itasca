import Exec.Spec.Counted
namespace Exec.Spec
open SpecExt

/-- A coherent source execution with a positive finite number of reductions
between consecutive configurations. -/
def InfiniteSource (initial : config) : Prop :=
  ∃ states : Nat → config, states 0 = initial ∧
    ∀ n, ∃ count, 0 < count ∧ StepsHN count (states n) [] (states (n+1))

/-- A finite initialization prefix can be absorbed into the first positive
chunk without changing the subsequent infinite execution. -/
theorem InfiniteSource.prepend {initial next : config}
    (infinite : InfiniteSource next) (steps : StepsH initial [] next) : InfiniteSource initial := by
  obtain ⟨states,first,edges⟩ := infinite
  obtain ⟨prefixCount,prefixSteps⟩ := stepsH_count steps
  refine ⟨(fun n => match n with | 0 => initial | n+1 => states (n+1)),rfl,?_⟩
  intro n
  cases n with
  | zero =>
    obtain ⟨count,positive,edge⟩ := edges 0
    rw [first] at edge
    exact ⟨prefixCount+count,by omega,by simpa using prefixSteps.trans edge⟩
  | succ n => exact edges (n+1)

end Exec.Spec
