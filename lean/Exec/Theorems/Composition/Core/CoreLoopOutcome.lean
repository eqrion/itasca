import Exec.Theorems.Composition.Core.CoreLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

def CoreLoopOutcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : CoreMachine M P view code expected) (result : ExecutionResult M P) : Prop :=
  (∃ final dispatches count,
    Spec.Iterations (CoreTransition memory hooks floats allocator) dispatches initial [] final ∧
    final.exec.frames.val = [] ∧ final.source.frames = [] ∧
    SpecExt.ResultsTyped final.source.store expected final.source.results ∧
    ValuesAt final.exec.slots.val 0 final.source.results ∧
    Spec.StepsHN count (Abs.decode initial.source) []
      ⟨⟨Store.decodeStore view code final.store,initial.source.ambient⟩,SpecExt.vals final.source.results⟩ ∧
    Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code final.store) ∧
    FrameStoreMetadata initial.store final.store ∧
    finishExecution (final.exec,final.store,final.platform,.Ok ()) = result) ∨
  (∃ previous dispatches count error finalExec finalStore finalPlatform,
    Spec.Iterations (CoreTransition memory hooks floats allocator) dispatches initial [] previous ∧
    Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
    runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform =
      .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
    CoreFailure allocator hooks previous.exec previous.store previous.platform previous.source error ∧
    Store.decodeStore view code finalStore = previous.source.store ∧
    CertifiedCoreStore view code finalStore ∧
    Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code finalStore) ∧
    FrameStoreMetadata initial.store finalStore ∧
    (finalStore.elems = initial.store.elems ∧ finalStore.datas = initial.store.datas) ∧
    finishExecution (finalExec,finalStore,finalPlatform,.Err error) = result)

theorem core_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : CoreMachine M P view code expected) (state : ExecutionState M P)
    (invariant : CoreLoopInvariant memory hooks floats allocator initial state)
    (stopped : ¬ActiveExecution state) :
    CoreLoopOutcome memory hooks floats allocator initial (finishExecution state) := by
  rcases state with ⟨exec,store,platform,status⟩
  obtain ⟨certified,invariant⟩ := invariant
  cases status with
  | Ok unit =>
    cases unit
    obtain ⟨machine,dispatches,run,sameExec,sameStore,samePlatform⟩ := invariant
    dsimp only at sameExec sameStore samePlatform
    subst exec
    subst store
    subst platform
    have empty : machine.exec.frames.val = [] := by
      have length : machine.exec.frames.length = 0 := by
        simp only [ActiveExecution,true_and,and_true,not_lt] at stopped
        omega
      exact List.length_eq_zero_iff.mp length
    obtain ⟨sourceEmpty,typed,represented⟩ := core_execution_finished machine.invariant empty
    obtain ⟨_,count,reductions⟩ := CoreMachine.history_source memory hooks floats allocator run
    obtain ⟨extension,metadata,ambient⟩ := CoreMachine.history_metadata memory hooks floats allocator run
    refine Or.inl ⟨machine,dispatches,count,run,empty,sourceEmpty,typed,represented,?_,extension,metadata,rfl⟩
    simpa only [Abs.decode,sourceEmpty,Abs.decodeFrames_nil,machine.invariant.storeEq,ambient] using reductions
  | Err error =>
    obtain ⟨machine,dispatches,run,failed,cause,decoded,extension,metadata,segments⟩ := invariant
    obtain ⟨_,count,reductions⟩ := CoreMachine.history_source memory hooks floats allocator run
    obtain ⟨prefixExtension,prefixMetadata,ambient⟩ := CoreMachine.history_metadata memory hooks floats allocator run
    refine Or.inr ⟨machine,dispatches,count,error,exec,store,platform,run,reductions,failed,cause,decoded,certified,
      Spec.extend_store_trans prefixExtension extension,prefixMetadata.trans metadata,?_,rfl⟩
    have prefixSegments := CoreMachine.history_segments memory hooks floats allocator run
    exact ⟨segments.1.trans prefixSegments.1,segments.2.trans prefixSegments.2⟩

theorem core_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : CoreMachine M P view code expected) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => CoreLoopOutcome memory hooks floats allocator initial result ⦄div := by
  apply WP.dspec_mono (core_loop_stops memory hooks floats allocator allocation interrupts view laws code initial)
  rintro result ⟨state,invariant,stopped,same⟩
  rw [←same]
  exact core_loop_finished memory hooks floats allocator initial state invariant stopped
end Exec.Theorems
