import Exec.Theorems.Composition.Recorded.RecordedLoopResult
import Exec.Platform.RecordingSpec
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Source outcomes use the exact list returned by the concrete loop recorder. -/
def RecordedLoopSourceOutcome {M P view code expected}
    (initial : EventfulMachine emission allowed M P view code expected) (result : ExecutionResult M P) (events : List HostEvent) : Prop :=
  let finalStore := result.2.2.2.2.2.1
  let status := result.2.2.2.2.2.2.2
  CertifiedSupportedStore emission allowed view code finalStore ∧
  FrameStorePrefix initial.store finalStore ∧
  Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code finalStore) ∧
  (status=.Ok () → ∃values,
    ResultsTyped (Store.decodeStore view code finalStore) expected values ∧
    Abs.Ownership.ValuesOwned (Store.ownershipBounds finalStore) values ∧
    ValuesAt result.2.1.val 0 values ∧
    StepsH (Abs.decode initial.source) events
      ⟨⟨Store.decodeStore view code finalStore,initial.source.ambient⟩,vals values⟩) ∧
  (∀error,status=.Err error →
    EventfulInvocationError (Abs.decode initial.source) events
      (Store.decodeStore view code finalStore) initial.source.ambient error)

/-- Lift the checked loop result to its actual writer computation. -/
theorem recorded_inv_loop_source_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : RecordedInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (initial : EventfulMachine emission allowed M P view code expected) (valid : Inv initial.store) :
    recordedInvokeLoop memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ()) []
      ⦃ (result,events) => Inv result.2.2.2.2.2.1 ∧ RecordedLoopSourceOutcome initial result events ⦄div := by
  apply Platform.Recording.lift_dspec _ _ _ _
    (recordedInvokeLoop_erase memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ()) [])
    (recorded_inv_loop_results memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨newValid,state,same,certified,kept,extension,stopped,count,events,normal,dispatches,writer,source⟩
  subst result
  rcases state with ⟨exec,store,platform,status⟩
  refine ⟨events,by simpa only [List.nil_append] using writer [],newValid,certified,kept,extension,?_,?_⟩
  · intro success
    change status=.Ok () at success
    simpa only [finishExecution,success] using source
  · intro error failed
    change status=.Err error at failed
    simpa only [finishExecution,failed] using source
end Exec.Theorems
