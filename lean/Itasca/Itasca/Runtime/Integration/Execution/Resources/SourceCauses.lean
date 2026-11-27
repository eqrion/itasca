import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.Integration.Execution.Resources.SourceDemand

/-!
# Source exclusion of dispatch causes

Source resource adequacy excludes classified event-bearing dispatch failures. This connects source demand to concrete boundary and host resource causes.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

theorem EventfulDispatchCause.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    {machine : EventfulMachine M P view code expected} {out error}
    (capacities : Representation.FunctionCapacities code machine.store)
    (cause : EventfulDispatchCause memory hooks floats allocator machine out error) :
    EventfulSourceResourceCause hooks allocator machine out error := by
  cases error with
  | Terminated =>
    rcases cause with ordinary | host
    · exact ordinary.1.interrupted
    · exact host.interrupted
  | Exhausted reason =>
    cases reason with
    | Values =>
      rcases cause with ordinary | host
      · obtain ⟨address,base,words,site,capacity,bound⟩ := ordinary.1.source_values view code machine.invariant.storeEq capacities machine.certified.typed
        exact ⟨address,base,site,Or.inl ⟨words,capacity,bound⟩⟩
      · obtain ⟨address,identity,base,params,results,site,signature,bound⟩ := host.source_values
        exact ⟨address,base,site,Or.inr ⟨identity,params,results,signature,bound⟩⟩
    | Allocation =>
      rcases cause with ordinary | host
      · exact Or.inl (ordinary.1.source_allocation view code machine.invariant.storeEq capacities machine.certified.typed)
      · exact Or.inr host.source_allocation
    | CallStack =>
      rcases cause with ordinary | host
      · exact Or.inl (ordinary.1.frame_depth machine.invariant.stack)
      · exact Or.inr host.host_overflow
    | Objects => exact cause.no_objects
  | _ => trivial

end Itasca.Integration
