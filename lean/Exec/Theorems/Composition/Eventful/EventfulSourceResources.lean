import Exec.Theorems.Api.InvocationObjectExclusion
import Exec.Theorems.Composition.Eventful.EventfulDispatchCauses
import Exec.Theorems.Composition.Supported.SupportedSourceResources
import Exec.Theorems.Composition.Supported.SupportedBoundaryCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Resource bounds at the actual reached machine. Host callbacks may change
limits, so these are deliberately the reached store's limits. -/
def EventfulSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (machine : EventfulMachine emission allowed M P view code expected)
    (out : EventfulDispatchResult M P) : runtime.ExecError → Prop
  | .Exhausted .Values => ∃ address base, SourceInvocationSite machine.source address base ∧
      ((∃ words,SourceCanonicalFunctionCapacity machine.source.store address words ∧
        machine.store.limits.max_values.val<base+words) ∨
       ∃ identity params results,HostFunction machine.source.store address identity params results ∧
        machine.store.limits.max_values.val<base+max (Code.slots params) (Code.slots results))
  | .Exhausted .Allocation => SourceInvocationAllocation allocator machine.source ∨
      ∃ address identity base params results,SourceInvocationSite machine.source address base ∧
        HostFunction machine.source.store address identity params results ∧ HostSignatureAllocation allocator params results base
  | .Exhausted .CallStack => machine.store.limits.max_frames.val≤Spec.frameDepth (Abs.decode machine.source) ∨
      ∃ identity p args defaults returned,
        hooks.call_host p machine.store identity args defaults=.ok (.Err .StackOverflow,out.2.2.2,out.2.2.1,returned)
  | .Terminated => ∃ after,hooks.interrupt machine.platform=.ok (.Terminate,after)
  | .Exhausted .Objects => False
  | _ => True

theorem EventfulDispatchCause.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {machine : EventfulMachine emission allowed M P view code expected} {out error}
    (capacities : Store.FunctionCapacities code machine.store)
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

/-- An actual failing dispatch is source-reachable and has source-bounded
requests. The reached invariant certifies functions introduced by prior hosts. -/
theorem EventfulLoopFailure.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {Inv : runtime.store.Store M → Prop}
    (capacities : ∀store,Inv store → Store.FunctionCapacities code store)
    {initial : EventfulMachine emission allowed M P view code expected} {result error}
    (failure : EventfulLoopFailure memory hooks floats allocator Inv
      (EventfulDispatchCause memory hooks floats allocator) initial result error) :
    ∃ previous : EventfulMachine emission allowed M P view code expected, ∃ events afterExec afterStore afterPlatform,
      StepsH (Abs.decode initial.source) events (Abs.decode previous.source) ∧ Inv previous.store ∧
      runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform=
        .ok (.Err error,afterExec,afterStore,afterPlatform) ∧
      EventfulSourceResourceCause hooks allocator previous (.Err error,afterExec,afterStore,afterPlatform) error ∧
      finishExecution (afterExec,afterStore,afterPlatform,.Err error)=result := by
  obtain ⟨previous,count,events,afterExec,afterStore,afterPlatform,history,valid,actual,cause,finished⟩ := failure
  obtain ⟨n,steps⟩ := EventfulMachine.history_source history
  exact ⟨previous,events,afterExec,afterStore,afterPlatform,steps.erase,valid,actual,
    cause.source_resources (capacities previous.store valid),finished⟩
end Exec.Theorems
