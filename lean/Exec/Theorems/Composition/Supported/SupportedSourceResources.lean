import Exec.Theorems.Composition.Supported.SupportedBoundaries
import Exec.Interp.Relations.SourceIndirectResources
import Exec.Store.Invariant.FunctionCapacities
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- All defined-call Values refusals retain a selected source call and its
source-certified frame requirement, including indirect calls. -/
theorem CumulativeFailure.source_values {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (failure : CumulativeFailure allocator hooks exec store platform source (.Exhausted .Values)) :
    ∃ address base words, SourceInvocationSite source address base ∧
      SourceCanonicalFunctionCapacity source.store address words ∧ store.limits.max_values.val<base+words := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,_⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨interpretation,indirect⟩
    · obtain ⟨address,base,words,site,capacity,exceeds⟩ := direct.source_values_canonical view code decoded capacities typed
      exact ⟨address,base,words,Or.inl site,capacity,exceeds⟩
    · obtain ⟨address,base,words,site,capacity,exceeds⟩ := indirect.source_values view code decoded capacities typed
      exact ⟨address,base,words,Or.inr site,capacity,exceeds⟩

theorem CumulativeFailure.source_allocation {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (decoded : source.store=Store.decodeStore view code store)
    (capacities : Store.FunctionCapacities code store)
    (typed : CoreFunctionsTyped view code store)
    (failure : CumulativeFailure allocator hooks exec store platform source (.Exhausted .Allocation)) :
    SourceInvocationAllocation allocator source := by
  rcases failure with ⟨⟨trap,kind,_⟩,_⟩ | ⟨kind,_⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨interpretation,indirect⟩
    · obtain ⟨address,base,words,site,capacity,refusal⟩ := direct.source_allocation_canonical view code decoded capacities typed
      exact ⟨address,base,words,site,capacity,refusal⟩
    · exact indirect.source_allocation view code decoded capacities typed

variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The bounded request is witnessed at a source-reachable call state. Its
limit is the invocation's original limit, even when prior steps mutate data. -/
theorem SupportedLoopOutcome.source_values {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (capacities : Store.FunctionCapacities code initial.store)
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2=.Err (.Exhausted .Values)) :
    ∃ source address base words, StepsH (Abs.decode initial.source) [] (Abs.decode source) ∧
      SourceInvocationSite source address base ∧ SourceCanonicalFunctionCapacity source.store address words ∧
      initial.store.limits.max_values.val<base+words := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  have metadata := (SupportedMachine.history_metadata memory hooks floats allocator history).2.1
  have retained := capacities.metadata metadata.functions metadata.instances metadata.types metadata.identity
  obtain ⟨address,base,words,site,capacity,exceeds⟩ := cause.source_values view code previous.invariant.storeEq retained previous.certified.typed
  have limits := SupportedMachine.history_limits memory hooks floats allocator history
  rw [limits] at exceeds
  exact ⟨previous.source,address,base,words,reductions.erase,site,capacity,exceeds⟩

theorem SupportedLoopOutcome.source_allocation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (capacities : Store.FunctionCapacities code initial.store)
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2=.Err (.Exhausted .Allocation)) :
    ∃ source, StepsH (Abs.decode initial.source) [] (Abs.decode source) ∧
      SourceInvocationAllocation allocator source := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  have metadata := (SupportedMachine.history_metadata memory hooks floats allocator history).2.1
  have retained := capacities.metadata metadata.functions metadata.instances metadata.types metadata.identity
  exact ⟨previous.source,reductions.erase,cause.source_allocation view code previous.invariant.storeEq retained previous.certified.typed⟩
end Exec.Theorems
