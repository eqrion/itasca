import Exec.Theorems.Composition.FloatCore.FloatCoreLoopOutcome
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt

theorem FloatCoreLoopOutcome.readback {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {expected : List valtype} {initial : FloatCoreMachine M P view code expected} {out : ExecutionResult M P}
    (outcome : FloatCoreLoopOutcome memory hooks floats allocator initial out) :
    let (_,words,_,_,_,afterStore,_,status) := out
    CertifiedFloatCoreStore view code afterStore ∧ FrameStoreMetadata initial.store afterStore ∧
      Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code afterStore) ∧
      (status = .Ok () → ∃ values,
        expected = values.map Code.valueType ∧
        (∀ value ∈ values, wf_val value) ∧ (∀ value ∈ values, ResultIndexFits value) ∧
        ValuesAt words.val 0 values ∧
        StepsH (Abs.decode initial.source) []
          ⟨⟨Store.decodeStore view code afterStore,initial.source.ambient⟩,vals values⟩) := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,rfl⟩ := success
    have tags : final.source.results.map Code.valueType = expected := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using Abs.results_type_of_typed typed
    refine ⟨final.certified,metadata,extension,fun _ => ⟨final.source.results,tags.symm,Spec.resultsTyped_wf typed,?_,represented,reductions.erase⟩⟩
    intro value member
    exact Store.owned_result_fits final.store value (final.owned.values.1 value member)
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,reductions,failed,cause,decoded,certified,extension,metadata,segments,rfl⟩ := failure
    exact ⟨certified,metadata,extension,by intro impossible; cases impossible⟩

theorem FloatCoreLoopOutcome.segment_vectors {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {expected : List valtype} {initial : FloatCoreMachine M P view code expected} {out : ExecutionResult M P}
    (outcome : FloatCoreLoopOutcome memory hooks floats allocator initial out) :
    let (_,_,_,_,_,afterStore,_,_) := out
    afterStore.elems = initial.store.elems ∧ afterStore.datas = initial.store.datas := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,rfl⟩ := success
    exact FloatCoreMachine.history_segments memory hooks floats allocator history
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,reductions,failed,cause,decoded,certified,extension,metadata,segments,rfl⟩ := failure
    exact segments

theorem float_core_loop_readback {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : FloatCoreMachine M P view code expected) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ (_,words,_,_,_,afterStore,_,status) =>
        CertifiedFloatCoreStore view code afterStore ∧ FrameStoreMetadata initial.store afterStore ∧
        Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code afterStore) ∧
        (status = .Ok () → ∃ values,
          expected = values.map Code.valueType ∧
          (∀ value ∈ values, wf_val value) ∧ (∀ value ∈ values, ResultIndexFits value) ∧
          ValuesAt words.val 0 values ∧
          StepsH (Abs.decode initial.source) []
            ⟨⟨Store.decodeStore view code afterStore,initial.source.ambient⟩,vals values⟩) ⦄div := by
  apply WP.dspec_mono (float_core_loop memory hooks floats allocator correct allocation interrupts view laws code initial)
  intro out outcome
  exact outcome.readback
end Exec.Theorems
