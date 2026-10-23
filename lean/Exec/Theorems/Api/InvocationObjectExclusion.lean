import Exec.Theorems.Api.InitialHostInvocationCauses
import Exec.Theorems.Composition.Eventful.EventfulDispatchCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Invocation does not allocate store objects. Every initial host failure is
setup/readback allocation, signature capacity, interrupt, or a host reply. -/
theorem InitialHostInvocationCause.no_objects {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
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
end Exec.Theorems
