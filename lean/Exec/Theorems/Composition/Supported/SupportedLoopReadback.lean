import Exec.Theorems.Composition.Supported.SupportedLoopOutcome
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem SupportedLoopOutcome.readback {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {expected : List valtype} {initial : SupportedMachine emission allowed M P view code expected} {out : ExecutionResult M P}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial out) :
    let (_,words,_,_,_,afterStore,_,status) := out
    CertifiedSupportedStore emission allowed view code afterStore ∧ FrameStoreMetadata initial.store afterStore ∧
      Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code afterStore) ∧
      Store.SegmentCounts initial.store afterStore ∧
      (status = .Ok () → ∃ values,
        expected = values.map Code.valueType ∧
        (∀ value ∈ values, wf_val value) ∧ (∀ value ∈ values, ResultIndexFits value) ∧
        ValuesAt words.val 0 values ∧
        StepsH (Abs.decode initial.source) []
          ⟨⟨Store.decodeStore view code afterStore,initial.source.ambient⟩,vals values⟩) := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,segments,limits,rfl⟩ := success
    have tags : final.source.results.map Code.valueType = expected := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using Abs.results_type_of_typed typed
    refine ⟨final.certified,metadata,extension,segments,fun _ => ⟨final.source.results,tags.symm,Spec.resultsTyped_wf typed,?_,represented,reductions.erase⟩⟩
    intro value member
    exact Store.owned_result_fits final.store value (final.owned.values.1 value member)
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,reductions,failed,cause,decoded,certified,extension,metadata,segments,limits,rfl⟩ := failure
    exact ⟨certified,metadata,extension,segments,by intro impossible; cases impossible⟩

theorem supported_loop_readback
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : SupportedMachine emission allowed M P view code expected) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ (_,words,_,_,_,afterStore,_,status) =>
        CertifiedSupportedStore emission allowed view code afterStore ∧ FrameStoreMetadata initial.store afterStore ∧
        Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code afterStore) ∧
      Store.SegmentCounts initial.store afterStore ∧
        (status = .Ok () → ∃ values,
          expected = values.map Code.valueType ∧
          (∀ value ∈ values, wf_val value) ∧ (∀ value ∈ values, ResultIndexFits value) ∧
          ValuesAt words.val 0 values ∧
          StepsH (Abs.decode initial.source) []
            ⟨⟨Store.decodeStore view code afterStore,initial.source.ambient⟩,vals values⟩) ⦄div := by
  apply WP.dspec_mono (supported_loop language memory hooks floats allocator correct allocation interrupts view laws code initial)
  intro out outcome
  exact outcome.readback
end Exec.Theorems
