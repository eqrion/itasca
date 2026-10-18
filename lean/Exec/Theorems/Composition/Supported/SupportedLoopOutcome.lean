import Exec.Theorems.Composition.Supported.SupportedLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

def SupportedLoopOutcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : SupportedMachine emission allowed M P view code expected) (result : ExecutionResult M P) : Prop :=
  (∃ final dispatches count,
    Spec.Iterations (SupportedTransition memory hooks floats allocator) dispatches initial [] final ∧
    final.exec.frames.val = [] ∧ final.source.frames = [] ∧
    SpecExt.ResultsTyped final.source.store expected final.source.results ∧
    ValuesAt final.exec.slots.val 0 final.source.results ∧
    Spec.StepsHN count (Abs.decode initial.source) []
      ⟨⟨Store.decodeStore view code final.store,initial.source.ambient⟩,SpecExt.vals final.source.results⟩ ∧
    Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code final.store) ∧
    FrameStoreMetadata initial.store final.store ∧
    Store.SegmentCounts initial.store final.store ∧
    final.store.limits = initial.store.limits ∧
    finishExecution (final.exec,final.store,final.platform,.Ok ()) = result) ∨
  (∃ previous dispatches count error finalExec finalStore finalPlatform,
    Spec.Iterations (SupportedTransition memory hooks floats allocator) dispatches initial [] previous ∧
    Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
    runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform =
      .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
    CumulativeFailure allocator hooks previous.exec previous.store previous.platform previous.source error ∧
    Store.decodeStore view code finalStore = previous.source.store ∧
    CertifiedSupportedStore emission allowed view code finalStore ∧
    Extend_store (Store.decodeStore view code initial.store) (Store.decodeStore view code finalStore) ∧
    FrameStoreMetadata initial.store finalStore ∧
    Store.SegmentCounts initial.store finalStore ∧
    finalStore.limits = initial.store.limits ∧
    finishExecution (finalExec,finalStore,finalPlatform,.Err error) = result)

theorem supported_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : SupportedMachine emission allowed M P view code expected) (state : ExecutionState M P)
    (invariant : SupportedLoopInvariant memory hooks floats allocator initial state)
    (stopped : ¬ActiveExecution state) :
    SupportedLoopOutcome memory hooks floats allocator initial (finishExecution state) := by
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
    obtain ⟨sourceEmpty,typed,represented⟩ := machine.invariant.finished empty
    obtain ⟨_,count,reductions⟩ := SupportedMachine.history_source memory hooks floats allocator run
    obtain ⟨extension,metadata,ambient⟩ := SupportedMachine.history_metadata memory hooks floats allocator run
    refine Or.inl ⟨machine,dispatches,count,run,empty,sourceEmpty,typed,represented,?_,extension,metadata,SupportedMachine.history_segments memory hooks floats allocator run,SupportedMachine.history_limits memory hooks floats allocator run,rfl⟩
    simpa only [Abs.decode,sourceEmpty,Abs.decodeFrames_nil,machine.invariant.storeEq,ambient] using reductions
  | Err error =>
    obtain ⟨machine,dispatches,run,failed,cause,decoded,extension,metadata,segments,limits⟩ := invariant
    obtain ⟨_,count,reductions⟩ := SupportedMachine.history_source memory hooks floats allocator run
    obtain ⟨prefixExtension,prefixMetadata,ambient⟩ := SupportedMachine.history_metadata memory hooks floats allocator run
    refine Or.inr ⟨machine,dispatches,count,error,exec,store,platform,run,reductions,failed,cause,decoded,certified,
      Spec.extend_store_trans prefixExtension extension,prefixMetadata.trans metadata,(SupportedMachine.history_segments memory hooks floats allocator run).trans segments,limits.trans (SupportedMachine.history_limits memory hooks floats allocator run),rfl⟩

theorem supported_loop
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
      ⦃ result => SupportedLoopOutcome memory hooks floats allocator initial result ⦄div := by
  apply WP.dspec_mono (supported_loop_stops language memory hooks floats allocator correct allocation interrupts view laws code initial)
  rintro result ⟨state,invariant,stopped,same⟩
  rw [←same]
  exact supported_loop_finished memory hooks floats allocator initial state invariant stopped
end Exec.Theorems
