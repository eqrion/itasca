import Exec.Theorems.Composition.World.ChosenWorldLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
def ChosenWorldLoopResult (choices : Spec.SourceChoices) {M P : Type} {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : ChosenWorld M P view expected) (result : ExecutionResult M P) : Prop :=
  let finalStore := result.2.2.2.2.2.1
  let status := result.2.2.2.2.2.2.2
  ∃ finalCode,Inv finalCode finalStore ∧ CertifiedSupportedStore view finalCode finalStore ∧
    FrameStorePrefix initial.machine.store finalStore ∧ Store.CodeAgreesOn initial.machine.store initial.code finalCode ∧
    Extend_store (Store.decodeStore view initial.code initial.machine.store) (Store.decodeStore view finalCode finalStore) ∧
    (status=.Ok () → ∃values events,
      ResultsTyped (Store.decodeStore view finalCode finalStore) expected values ∧
      Abs.Ownership.ValuesOwned (Store.ownershipBounds finalStore) values ∧ ValuesAt result.2.1.val 0 values ∧
      (∃ count,Spec.ChosenStepsN choices initial.occurrence count (Abs.decode initial.machine.source) events
        ⟨⟨Store.decodeStore view finalCode finalStore,initial.machine.source.ambient⟩,vals values⟩)) ∧
    (∀error,status=.Err error → ∃events,ChosenEventfulInvocationError choices initial.occurrence (Abs.decode initial.machine.source) events
      (Store.decodeStore view finalCode finalStore) initial.machine.source.ambient error)

theorem chosen_world_loop_finished {choices : Spec.SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : ChosenWorld M P view expected) (state : ExecutionState M P)
    (invariant : ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial state)
    (stopped : ¬ActiveExecution state) : ChosenWorldLoopResult choices Inv initial (finishExecution state) := by
  rcases state with ⟨exec,store,platform,status⟩
  cases status with
  | Ok value =>
    cases value
    obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
    have unrecorded := world_recorded_history (ChosenWorld.history_erases history)
    have metadata := EventfulWorld.history_metadata unrecorded
    have ambient := EventfulWorld.history_ambient unrecorded
    refine ⟨current.code,valid,current.machine.certified,metadata.2.1,metadata.2.2,metadata.1,?_,?_⟩
    · intro success
      have empty : current.machine.exec.frames.val=[] := by
        have length : current.machine.exec.frames.length=0 := by
          simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
          omega
        exact List.length_eq_zero_iff.mp length
      obtain ⟨sourceEmpty,typed,represented⟩ := current.machine.invariant.finished empty
      obtain ⟨n,clock,reductions⟩ := ChosenWorld.history_source history
      refine ⟨current.machine.source.results,events,?_,current.machine.owned.values.1,represented,?_⟩
      · simpa only [finishExecution,current.machine.invariant.storeEq] using typed
      · refine ⟨n,?_⟩
        simpa only [finishExecution,Abs.decode,sourceEmpty,Abs.decodeFrames_nil,current.machine.invariant.storeEq,ambient] using reductions
    · intro error impossible
      cases impossible
  | Err error =>
    obtain ⟨current,valid,count,events,history,actual,afterCode,fresh,certified,retained,agrees,extension,outcome,cause⟩ := invariant
    have unrecorded := world_recorded_history (ChosenWorld.history_erases history)
    have metadata := EventfulWorld.history_metadata unrecorded
    have ambient := EventfulWorld.history_ambient unrecorded
    refine ⟨afterCode,fresh,certified,metadata.2.1.trans retained,
      metadata.2.2.trans_prefix metadata.2.1 agrees,Spec.extend_store_trans metadata.1 extension,?_,?_⟩
    · intro impossible
      cases impossible
    · intro reported failed
      have same : error=reported := core.result.Result.Err.inj failed
      subst reported
      obtain ⟨n,clock,reductions⟩ := ChosenWorld.history_source history
      refine ⟨events++stepHostEvents current.machine.exec current.machine.store (.Err error,exec,store,platform),?_⟩
      rw [clock] at outcome
      simpa only [finishExecution,ambient] using outcome.prepend reductions


end Exec.Theorems
