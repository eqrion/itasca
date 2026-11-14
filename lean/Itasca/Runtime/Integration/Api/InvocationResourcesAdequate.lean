import Itasca.Runtime.Integration.Api.InitialHostInvocationCauses
import Itasca.Runtime.Integration.Execution.Resources.DispatchCauses
import Itasca.Runtime.Integration.Api.InvocationEntryResources
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Spec.MemoryGrowth
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.SourceMachine.Stateful.TableRead
import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.Spec.Simd.Pairwise
import Itasca.Runtime.Spec.Simd.ExtendLanes
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.SourceMachine.Float.Transition
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.SourceMachine.Core.SelectPositive
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.SourceMachine.Supported.CumulativeStep
import Itasca.Runtime.Integration.Execution.Resources.SourceDemand
import Itasca.Runtime.Interp.Calls.IndirectResolve

/-!
Sections, each formerly its own module: InvocationObjectExclusion, InvocationResourcesAdequate.
-/

/-! ## InvocationObjectExclusion -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Invocation does not allocate store objects. Every initial host failure is
setup/readback allocation, signature capacity, interrupt, or a host reply. -/
theorem InitialHostInvocationCause.no_objects {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .Objects)) : False := by
  rcases cause with ⟨_,setup⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,refused⟩
  · exact setup
  · cases impossible
  · simpa only [HostCallCauses,failed,HostPreparationCause] using refused

/-- A failed actual dispatch has no object-limit refusal branch. Store growth
instructions report their specified numeric failure result instead. -/
theorem EventfulDispatchCause.no_objects

    {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {machine : EventfulMachine M P view code expected} {out}
    (cause : EventfulDispatchCause memory hooks floats allocator machine out (.Exhausted .Objects)) : False := by
  rcases cause with ordinary | host
  · have impossible := ordinary.1.kind
    simp at impossible
  · obtain ⟨failed,index,raw,pc,address,signature,base,identity,found,next,site,actual,refused⟩ := host
    simpa only [HostCallCauses,failed,HostPreparationCause] using refused
end Itasca.Runtime.Integration

end

/-! ## InvocationResourcesAdequate -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec Itasca.Runtime.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

end Itasca.Runtime.Integration

end
