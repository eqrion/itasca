import Exec.Theorems.Composition.World.WorldRecordedLoop
import Exec.Theorems.Composition.Eventful.EventfulSourceResources
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A failed dispatch retains its actual reached world and source-sized
resource request, even when earlier callbacks published new modules. -/
def WorldLoopResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected)
    (result : ExecutionResult M P) (error : runtime.ExecError) : Prop :=
  ∃ previous : EventfulWorld M P view expected, ∃ count events afterExec afterStore afterPlatform,
    Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) count initial events previous ∧
    StepsH (Abs.decode initial.machine.source) events (Abs.decode previous.machine.source) ∧
    Inv previous.code previous.machine.store ∧
    runtime.interp.step memory hooks floats allocator previous.machine.exec previous.machine.store previous.machine.platform=
      .ok (.Err error,afterExec,afterStore,afterPlatform) ∧
    EventfulSourceResourceCause hooks allocator previous.machine (.Err error,afterExec,afterStore,afterPlatform) error ∧
    finishExecution (afterExec,afterStore,afterPlatform,.Err error)=result

theorem WorldLoopInvariant.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    (capacities : ∀c store,Inv c store → Store.FunctionCapacities c store)
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
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (capacities : ∀c store,Inv c store → Store.FunctionCapacities c store)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected) (valid : Inv initial.code initial.machine.store) :
    recordedInvokeLoop memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) []
      ⦃ (result,events) => WorldRecordedLoopOutcome Inv initial result events ∧
        ∀error,result.2.2.2.2.2.2.2=.Err error → WorldLoopResourceCause memory hooks floats allocator Inv initial result error ⦄div := by
  apply Platform.Recording.lift_dspec _ _ _ _
    (recordedInvokeLoop_erase memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) [])
    (world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,invariant,stopped,same⟩
  obtain ⟨events,writer,source⟩ := world_recorded_loop_finished memory hooks floats allocator Inv initial state invariant stopped
  subst result
  refine ⟨events,by simpa only [List.nil_append] using writer [],source,?_⟩
  intro error failed
  apply invariant.source_resources capacities
  simpa only [finishExecution] using failed
end Exec.Theorems
