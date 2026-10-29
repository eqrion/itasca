import Itasca.Runtime.Integration.Execution.Resources.FailureNormalization
import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem Machine.Advance.prepend_normalization {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : SourceMachine.AFrame} {s : _root_.store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    (advance : Machine.Advance view code store exec expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩) :
    Machine.Advance view code store exec expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,ownership,ambientEq,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.prepend_normalization chain s ambient rest typed,
    fun bound owned => ownership bound (chain.ownership.stateful owned),ambientEq,fun bound h => bounded bound (chain.code_bound h)⟩

theorem SupportedStepOutcome.prepend_normalization {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {expected : List valtype}
    {codeLength pc count : Nat} {before middle : SourceMachine.AFrame} {s : _root_.store} {ambient : frame} {rest : List SourceMachine.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    (outcome : SupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩ out) :
    SupportedStepOutcome allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ out := by
  obtain ⟨mutation,transition⟩ := outcome
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    simp only [status] at transition ⊢
    exact Machine.Advance.prepend_normalization chain typed transition
  | Err error =>
    simp only [status] at transition ⊢
    exact ⟨transition.1.prepend_normalization chain typed,transition.2⟩
end Itasca.Runtime.Integration
