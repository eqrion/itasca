import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Execution.World.NonhostStep
import Itasca.Runtime.Integration.Execution.Resources.SourceCauses

/-!
# Source resources through recorded loops

The evolving-world loop invariant carries source resource conditions to actual recorded results. Invocation resource completeness consumes this correspondence.
-/
namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly Itasca.Interp

/-- Erase the simulation certificates from an actual failing history, retaining
the reached source configuration, store interpretation, invariant and refusal. -/
theorem WorldLoopResourceCause.source {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    {first : EventfulWorld M P view expected} {initial : config}
    {result : ExecutionResult M P} {error : runtime.ExecError}
    (entry : StepH initial [] (SourceMachine.decode first.machine.source))
    (cause : WorldLoopResourceCause memory hooks floats allocator Inv first result error) :
    ∃ source reachedCode reachedStore reachedPlatform nextPlatform events,
      StepsH initial events (SourceMachine.decode source) ∧
      source.store = Representation.decodeStore view reachedCode reachedStore ∧
      Inv reachedCode reachedStore ∧
      DispatchResourceCause hooks allocator source reachedStore reachedPlatform
        result.2.2.2.2.2.1 nextPlatform error := by
  obtain ⟨previous,count,events,afterExec,afterStore,afterPlatform,history,steps,held,actual,refusal,finished⟩ := cause
  subst result
  refine ⟨previous.machine.source,previous.code,previous.machine.store,
    previous.machine.platform,afterPlatform,events,?_,previous.machine.invariant.storeEq,held,refusal⟩
  simpa only [List.nil_append] using StepsH.cons entry steps

theorem WorldLoopInvariant.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop}
    (capacities : ∀c store,Inv c store → Representation.FunctionCapacities c store)
    {initial : EventfulWorld M P view expected} {state : ExecutionState M P} {error : runtime.ExecError}
    (invariant : WorldLoopInvariant memory hooks floats allocator Inv initial state)
    (failed : state.2.2.2=.Err error) :
    WorldLoopResourceCause memory hooks floats allocator Inv initial (finishExecution state) error := by
  rcases state with ⟨exec,store,platform,status⟩
  dsimp only at failed
  subst status
  obtain ⟨previous,valid,count,events,history,actual,afterCode,fresh,certified,retained,agrees,extension,outcome,cause⟩ := invariant
  obtain ⟨n,source⟩ := EventfulWorld.history_source (world_recorded_history history)
  exact ⟨previous,count,events,exec,store,platform,history,source.erase,valid,actual,
    cause.source_resources (capacities previous.code previous.machine.store valid),rfl⟩

theorem world_recorded_loop_resource_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (capacities : ∀c store,Inv c store → Representation.FunctionCapacities c store)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected) (valid : Inv initial.code initial.machine.store) :
    recordedInvokeLoop memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) []
      ⦃ (result,events) => WorldRecordedLoopOutcome Inv initial result events ∧
        ∀error,result.2.2.2.2.2.2.2=.Err error → WorldLoopResourceCause memory hooks floats allocator Inv initial result error ⦄div := by
  apply Platform.Recording.lift_dspec _ _ _ _
    (recorded_invoke_loop_erase memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) [])
    (world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,invariant,stopped,same⟩
  obtain ⟨events,writer,source⟩ := world_recorded_loop_finished memory hooks floats allocator Inv initial state invariant stopped
  subst result
  refine ⟨events,by simpa only [List.nil_append] using writer [],source,?_⟩
  intro error failed
  apply invariant.source_resources capacities
  simpa only [finishExecution] using failed
end Itasca.Integration
