import Itasca.Runtime.Theorems.Composition.Supported.SupportedExecutionOutcome
import Itasca.Runtime.Interp.Machines.Slice.SliceMeasure
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem StructuredMachine.Advance.widen {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : Abs.AState}
    (advance : StructuredMachine.Advance view code store exec expected small pc pending before) (bound : small ≤ large) :
    StructuredMachine.Advance view code store exec expected large pc pending before := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambient,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.widen bound,ownership,ambient,bounded⟩

theorem SupportedStepOutcome.widen {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : Abs.AState} {out}
    (outcome : SupportedStepOutcome allocator hooks view code exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    SupportedStepOutcome allocator hooks view code exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact StructuredMachine.Advance.widen transition bound
  | Err error => simpa only [status] using transition

end Itasca.Runtime.Theorems
