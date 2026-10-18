import Exec.Theorems.Composition.Uniform.UniformSupportedOutcome
import Exec.Theorems.Composition.Supported.SupportedMeasure
import Exec.Theorems.Composition.Supported.SupportedNormalizeOutcome
namespace Exec.Interp
 theorem UniformConcreteSim.prepend_source {beforePC afterPC beforePending afterPending before middle after events}
    (normal : Abs.NextSim before middle)
    (step : UniformConcreteSim beforePC afterPC beforePending afterPending middle after events) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events := by
  rcases normal with ⟨same,_⟩ | ⟨count,positive,steps⟩
  · simpa only [UniformConcreteSim,same] using step
  · simpa only [List.nil_append] using step.prepend_steps steps
 theorem UniformConcreteSim.prepend_normalization {count before middle}
    (chain : ErasedSteps count before middle) (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    {pc target pending after events}
    (simulation : UniformConcreteSim pc target false pending ⟨s,ambient,middle::rest,[]⟩ after events) :
    UniformConcreteSim pc target false pending ⟨s,ambient,before::rest,[]⟩ after events := by
  rcases (chain.sound s ambient rest typed).2 with ⟨_,same⟩ | prefixSimulation
  · simpa only [same] using simulation
  · exact simulation.prepend_source prefixSimulation
end Exec.Interp
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem StructuredMachine.UniformAdvance.widen {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {small large pc : Nat} {pending : Bool} {before : Abs.AState}
    (advance : StructuredMachine.UniformAdvance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store exec expected small pc pending before) (bound : small ≤ large) :
    StructuredMachine.UniformAdvance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store exec expected large pc pending before := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,uniform,ownership,ambient,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.widen bound,uniform,ownership,ambient,bounded⟩

theorem UniformSupportedStepOutcome.widen {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {expected : List valtype} {small large pc : Nat}
    {pending : Bool} {source : Abs.AState} {out}
    (outcome : UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected small pc pending source out)
    (bound : small ≤ large) :
    UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected large pc pending source out := by
  obtain ⟨sameStore, transition⟩ := outcome
  refine ⟨sameStore, ?_⟩
  cases status : out.1 with
  | Ok u =>
    simp only [status] at transition ⊢
    exact StructuredMachine.UniformAdvance.widen transition bound
  | Err error => simpa only [status] using transition

end Exec.Theorems

namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem StructuredMachine.UniformAdvance.prepend_normalization {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (advance : StructuredMachine.UniformAdvance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store exec expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩) :
    StructuredMachine.UniformAdvance emission (Abs.SupportedState allowed) Abs.Ownership.StatefulOwned view code store exec expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ := by
  obtain ⟨nextPC,nextPending,after,invariant,simulation,uniform,ownership,ambientEq,bounded⟩ := advance
  exact ⟨nextPC,nextPending,after,invariant,simulation.prepend_normalization chain s ambient rest typed,
    uniform.prepend_normalization chain s ambient rest typed,
    fun bound owned => ownership bound (chain.ownership.stateful owned),ambientEq,fun bound h => bounded bound (chain.codeBound h)⟩

theorem UniformSupportedStepOutcome.prepend_normalization {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P} {expected : List valtype}
    {codeLength pc count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s,ambient,before::rest,[]⟩)
    (outcome : UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,middle::rest,[]⟩ out) :
    UniformSupportedStepOutcome emission allowed allocator hooks view code exec store platform expected codeLength pc false ⟨s,ambient,before::rest,[]⟩ out := by
  obtain ⟨mutation,transition⟩ := outcome
  refine ⟨mutation,?_⟩
  cases status : out.1 with
  | Ok unit =>
    simp only [status] at transition ⊢
    exact StructuredMachine.UniformAdvance.prepend_normalization chain typed transition
  | Err error =>
    simp only [status] at transition ⊢
    exact ⟨transition.1.prepend_normalization chain typed,transition.2⟩
end Exec.Theorems
