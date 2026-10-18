import Exec.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Exec.Interp.Machines.Slice.SliceMeasure
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem Cumulative.Advance.widen {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : Abs.AState}
    (advance : Cumulative.Advance view code store exec expected small pc pending before) (bound : small ≤ large) :
    Cumulative.Advance view code store exec expected large pc pending before := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambient,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.widen bound,ownership,ambient,bounded⟩

theorem CumulativeStepOutcome.widen {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : Abs.AState} {out}
    (outcome : CumulativeStepOutcome allocator hooks view code exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    CumulativeStepOutcome allocator hooks view code exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact Cumulative.Advance.widen transition bound
  | Err error => simpa only [status] using transition

end Exec.Theorems
