import Exec.Theorems.Composition.World.WorldRecordedHistory
import Exec.Platform.RecordingSpec
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

def WorldRecordedLoopOutcome {M P : Type} {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected) (result : ExecutionResult M P) (events : List HostEvent) : Prop :=
  let finalStore := result.2.2.2.2.2.1
  let status := result.2.2.2.2.2.2.2
  ∃ finalCode,Inv finalCode finalStore ∧ CertifiedSupportedStore view finalCode finalStore ∧
    FrameStorePrefix initial.machine.store finalStore ∧ Store.CodeAgreesOn initial.machine.store initial.code finalCode ∧
    Extend_store (Store.decodeStore view initial.code initial.machine.store) (Store.decodeStore view finalCode finalStore) ∧
    (status=.Ok () → ∃values,
      ResultsTyped (Store.decodeStore view finalCode finalStore) expected values ∧
      Abs.Ownership.ValuesOwned (Store.ownershipBounds finalStore) values ∧ ValuesAt result.2.1.val 0 values ∧
      StepsH (Abs.decode initial.machine.source) events
        ⟨⟨Store.decodeStore view finalCode finalStore,initial.machine.source.ambient⟩,vals values⟩) ∧
    (∀error,status=.Err error → EventfulInvocationError (Abs.decode initial.machine.source) events
      (Store.decodeStore view finalCode finalStore) initial.machine.source.ambient error)

theorem world_recorded_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : EventfulWorld M P view expected) (state : ExecutionState M P)
    (invariant : WorldLoopInvariant memory hooks floats allocator Inv initial state)
    (stopped : ¬ActiveExecution state) : ∃events,
      (∀prior,recordedInvokeLoop memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) prior=
        .ok (finishExecution state,prior++events)) ∧
      WorldRecordedLoopOutcome Inv initial (finishExecution state) events := by
  rcases state with ⟨exec,store,platform,status⟩
  cases status with
  | Ok value =>
    cases value
    obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
    have unrecorded := world_recorded_history history
    have metadata := EventfulWorld.history_metadata unrecorded
    have ambient := EventfulWorld.history_ambient unrecorded
    refine ⟨events,world_recorded_history_stopped_writer history stopped,current.code,valid,current.machine.certified,metadata.2.1,metadata.2.2,metadata.1,?_,?_⟩
    · intro success
      have empty : current.machine.exec.frames.val=[] := by
        have length : current.machine.exec.frames.length=0 := by
          simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
          omega
        exact List.length_eq_zero_iff.mp length
      obtain ⟨sourceEmpty,typed,represented⟩ := current.machine.invariant.finished empty
      obtain ⟨n,reductions⟩ := EventfulWorld.history_source unrecorded
      refine ⟨current.machine.source.results,?_,current.machine.owned.values.1,represented,?_⟩
      · simpa only [finishExecution,current.machine.invariant.storeEq] using typed
      · simpa only [finishExecution,Abs.decode,sourceEmpty,Abs.decodeFrames_nil,current.machine.invariant.storeEq,ambient] using reductions.erase
    · intro error impossible
      cases impossible
  | Err error =>
    obtain ⟨current,valid,count,events,history,actual,afterCode,fresh,certified,retained,agrees,extension,outcome,cause⟩ := invariant
    have unrecorded := world_recorded_history history
    have metadata := EventfulWorld.history_metadata unrecorded
    have ambient := EventfulWorld.history_ambient unrecorded
    let terminal := stepHostEvents current.machine.exec current.machine.store (.Err error,exec,store,platform)
    refine ⟨events++terminal,?_,afterCode,fresh,certified,metadata.2.1.trans retained,
      metadata.2.2.trans_prefix metadata.2.1 agrees,Spec.extend_store_trans metadata.1 extension,?_,?_⟩
    · intro prior
      rw [world_recorded_history_writer_prefix history prior,recordedInvokeLoop_step memory hooks floats allocator actual]
      simpa only [terminal,List.append_assoc] using recordedInvokeLoop_stopped memory hooks floats allocator (exec,store,platform,.Err error) (by simp [ActiveExecution]) ((prior++events)++terminal)
    · intro impossible
      cases impossible
    · intro reported failed
      have same : error=reported := core.result.Result.Err.inj failed
      subst reported
      obtain ⟨n,reductions⟩ := EventfulWorld.history_source unrecorded
      simpa only [finishExecution,ambient] using outcome.prepend reductions.erase

/-- The actual loop recorder follows an evolving code interpretation and returns
exactly the source trace, including its final failing host dispatch. -/
theorem world_recorded_loop_results {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld M P view expected) (valid : Inv initial.code initial.machine.store) :
    recordedInvokeLoop memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) []
      ⦃ (result,events) => WorldRecordedLoopOutcome Inv initial result events ⦄div := by
  apply Platform.Recording.lift_dspec _ _ _ _
    (recordedInvokeLoop_erase memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) [])
    (world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,invariant,stopped,same⟩
  obtain ⟨events,writer,source⟩ := world_recorded_loop_finished memory hooks floats allocator Inv initial state invariant stopped
  subst result
  exact ⟨events,by simpa only [List.nil_append] using writer [],source⟩
end Exec.Theorems
