import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Interp.Machines.Slice.SliceMeasure
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem ChosenConcreteSim.widen {choices : Spec.SourceChoices} {occurrence : Nat}
    {small large beforePC afterPC : Nat} {beforePending afterPending : Bool} {before after : Abs.AState}
    (simulation : ChosenConcreteSim choices occurrence small beforePC afterPC beforePending afterPending before after)
    (bound : small≤large) :
    ChosenConcreteSim choices occurrence large beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same,decrease⟩ | steps
  · exact .inl ⟨same,dispatchMeasure_widen bound decrease⟩
  · exact .inr steps

theorem StructuredMachine.ChosenAdvance.widen {choices : Spec.SourceChoices} {occurrence : Nat} {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : Abs.AState}
    (advance : StructuredMachine.ChosenAdvance choices occurrence emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store exec expected small pc pending before) (bound : small ≤ large) :
    StructuredMachine.ChosenAdvance choices occurrence emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store exec expected large pc pending before := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambient,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,ChosenConcreteSim.widen simulation bound,ownership,ambient,bounded⟩

theorem ChosenSupportedStepOutcome.widen {choices : Spec.SourceChoices} {occurrence : Nat} {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : Abs.AState} {out}
    (outcome : ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact StructuredMachine.ChosenAdvance.widen transition bound
  | Err error => simpa only [status] using transition

end Exec.Theorems
