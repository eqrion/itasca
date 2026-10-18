import Exec.Interp.FloatCore.Outcome
import Exec.Interp.Machines.Slice.SliceMeasure
namespace Exec.Interp
open Aeneas Aeneas.Std
theorem FloatCoreAdvance.widen {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : Abs.AState}
    (advance : FloatCoreAdvance view code store exec expected small pc pending before) (bound : small ≤ large) :
    FloatCoreAdvance view code store exec expected large pc pending before := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambient,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.widen bound,ownership,ambient,bounded⟩

theorem FloatCoreOutcome.widen {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : Abs.AState} {out}
    (outcome : FloatCoreOutcome allocator hooks view code exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    FloatCoreOutcome allocator hooks view code exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact transition.widen bound
  | Err error => simpa only [status] using transition

end Exec.Interp
