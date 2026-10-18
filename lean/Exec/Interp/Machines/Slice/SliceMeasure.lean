import Exec.Interp.Machines.Slice.SliceOutcome

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Increasing the fixed code bound preserves strict administrative progress.
This allows calls and returns to use one invocation-wide potential. -/
theorem dispatchMeasure_widen {small large beforePC afterPC : Nat}
    {beforePending afterPending : Bool} {before after : Abs.AState}
    (bound : small ≤ large)
    (decrease : dispatchMeasure afterPending small afterPC after < dispatchMeasure beforePending small beforePC before) :
    dispatchMeasure afterPending large afterPC after < dispatchMeasure beforePending large beforePC before := by
  by_cases source : Abs.administrativeMeasure after < Abs.administrativeMeasure before
  · exact dispatchMeasure_source_any beforePending afterPending large beforePC afterPC source
  · have same : Abs.administrativeMeasure after = Abs.administrativeMeasure before := by
      by_contra different
      have reverse : Abs.administrativeMeasure before < Abs.administrativeMeasure after := by omega
      have impossible := dispatchMeasure_source_any afterPending beforePending small afterPC beforePC reverse
      omega
    cases beforePending <;> cases afterPending <;>
      simp only [dispatchMeasure, same, Bool.false_eq_true, ite_false, ite_true] at decrease ⊢ <;> omega

theorem ConcreteSim.widen {small large beforePC afterPC : Nat}
    {beforePending afterPending : Bool} {before after : Abs.AState}
    (simulation : ConcreteSim small beforePC afterPC beforePending afterPending before after)
    (bound : small ≤ large) :
    ConcreteSim large beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | steps
  · exact Or.inl ⟨same, dispatchMeasure_widen bound decrease⟩
  · exact Or.inr steps

theorem SliceAdvance.widen {M : Type} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : Abs.AState}
    (advance : SliceAdvance store exec expected small pc pending before) (bound : small ≤ large) :
    SliceAdvance store exec expected large pc pending before := by
  obtain ⟨after, nextPC, nextPending, invariant, sameStore, sameAmbient, simulation, bounded, references⟩ := advance
  exact ⟨after, nextPC, nextPending, invariant, sameStore, sameAmbient, simulation.widen bound, bounded, references⟩

theorem SliceOutcome.widen {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : Abs.AState} {out}
    (outcome : SliceOutcome allocator hooks exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    SliceOutcome allocator hooks exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact transition.widen bound
  | Err error => simpa only [status] using transition

end Exec.Interp
