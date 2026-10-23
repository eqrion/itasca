import Exec.Theorems.Composition.Recorded.RecordedLoop
import Exec.Theorems.Composition.Recorded.RecordedHistoryTrace
import Exec.Theorems.Api.RecordedHistoryWriter
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- One concrete dispatch log is retained together with the source execution
using exactly those labels. A final reported error includes its dispatch. -/
def RecordedLoopTrace {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : EventfulMachine emission allowed M P view code expected) (state : ExecutionState M P) : Prop :=
  ∃ count events,
    NormalTrace (executionBody memory hooks floats allocator) count
      (initial.exec,initial.store,initial.platform,.Ok ()) (finishExecution state) ∧
    (∀ prior,recordedSteps memory hooks floats allocator count initial.exec initial.store initial.platform prior =
      .ok ((state.2.2.2,state.1,state.2.1,state.2.2.1),prior++events)) ∧
    (∀ prior,recordedInvokeLoop memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ()) prior=
      .ok (finishExecution state,prior++events)) ∧
    match state.2.2.2 with
    | .Ok _ => ∃values,
        ResultsTyped (Store.decodeStore view code state.2.1) expected values ∧
        Abs.Ownership.ValuesOwned (Store.ownershipBounds state.2.1) values ∧
        ValuesAt state.1.slots.val 0 values ∧
        StepsH (Abs.decode initial.source) events
          ⟨⟨Store.decodeStore view code state.2.1,initial.source.ambient⟩,vals values⟩
    | .Err error => EventfulInvocationError (Abs.decode initial.source) events
        (Store.decodeStore view code state.2.1) initial.source.ambient error

theorem recorded_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : EventfulMachine emission allowed M P view code expected) (state : ExecutionState M P)
    (invariant : RecordedLoopInvariant memory hooks floats allocator initial state)
    (stopped : ¬ActiveExecution state) :
    RecordedLoopTrace memory hooks floats allocator initial state := by
  rcases state with ⟨exec,store,platform,status⟩
  obtain ⟨certified,retained,extension,invariant⟩ := invariant
  cases status with
  | Ok unit =>
    cases unit
    obtain ⟨machine,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
    refine ⟨count,events,recorded_history_stopped_trace history stopped,fun prior=>(recorded_history_exact history prior).1,fun prior=>recorded_history_stopped_writer history stopped prior,?_⟩
    have empty : machine.exec.frames.val=[] := by
      have length : machine.exec.frames.length=0 := by
        simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
        omega
      exact List.length_eq_zero_iff.mp length
    obtain ⟨sourceEmpty,typed,represented⟩ := machine.invariant.finished empty
    obtain ⟨count,reductions⟩ := (recorded_history_exact history []).2
    have ambient := (EventfulMachine.history_metadata (recorded_history_eventful history)).2.2
    refine ⟨machine.source.results,?_,machine.owned.values.1,represented,?_⟩
    · simpa only [machine.invariant.storeEq] using typed
    · simpa only [Abs.decode,sourceEmpty,Abs.decodeFrames_nil,machine.invariant.storeEq,ambient] using reductions.erase
  | Err error =>
    obtain ⟨machine,count,events,more,history,failed⟩ := invariant
    exact ⟨count+1,events++more,recorded_history_failed_trace history failed,fun prior=>(recorded_history_error_exact history failed prior).1,fun prior=>recorded_history_failed_writer history failed prior,
      (recorded_history_error_exact history failed []).2⟩

/-- The actual loop result, its API invariant, and exact concrete/source log.
The event list is chosen once, by the recorded dispatches. -/
def RecordedLoopResult {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : EventfulMachine emission allowed M P view code expected) (result : ExecutionResult M P) : Prop :=
  ∃state, finishExecution state=result ∧
    CertifiedSupportedStore emission allowed view code state.2.1 ∧ FrameStorePrefix initial.store state.2.1 ∧
    Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code state.2.1) ∧
    ¬ActiveExecution state ∧ RecordedLoopTrace memory hooks floats allocator initial state

theorem recorded_inv_loop_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : RecordedInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (initial : EventfulMachine emission allowed M P view code expected) (valid : Inv initial.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => Inv result.2.2.2.2.2.1 ∧ RecordedLoopResult memory hooks floats allocator initial result ⦄div := by
  apply WP.dspec_mono (recorded_inv_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,valid,invariant,stopped,same⟩
  refine ⟨?_,state,same,invariant.1,invariant.2.1,invariant.2.2.1,stopped,recorded_loop_finished memory hooks floats allocator initial state invariant stopped⟩
  rw [←same]
  exact valid
end Exec.Theorems
