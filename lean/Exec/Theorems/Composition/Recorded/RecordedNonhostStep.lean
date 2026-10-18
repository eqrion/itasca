import Exec.Theorems.Composition.Eventful.EventfulNonhostStep
import Exec.Theorems.Composition.Eventful.EventfulErrors
import Exec.Theorems.Composition.Recorded.RecordedEventfulHistory
import Exec.Theorems.Host.HostRecordingBoundary
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem recorded_inv_silent_or_host
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
    (Inv : runtime.store.Store M → Prop)
    (update : ∀before after,Inv before → CumulativeStoreMutation view code before after → Inv after)
    {expected : List valtype} (machine : EventfulMachine emission allowed M P view code expected)
    (valid : Inv machine.store)
    (active : 0 < machine.exec.frames.length)
    (silent : hostStepAddress machine.exec machine.store=none) :
    StructuredHostSite emission allowed view code machine.exec machine.store expected machine.pc machine.pending machine.source ∨
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      Inv out.2.2.1 ∧
      (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        RecordedEventfulTransition memory hooks floats allocator machine events next) ∧
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix machine.store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error →
        EventfulInvocationError (Abs.decode machine.source) (stepHostEvents machine.exec machine.store out)
          (Store.decodeStore view code out.2.2.1) machine.source.ambient error ⦄ := by
  rcases step_supported_host_site language memory hooks floats allocator correct allocation interrupts view laws code
    machine.exec machine.store machine.platform machine.source expected machine.pc machine.pending
    machine.invariant.storeEq machine.certified.shape machine.certified.storeSyntax machine.certified.segmentBounds
    machine.certified.compiled machine.certified.typed machine.owned machine.invariant active with host | operation
  · exact Or.inl host
  · apply Or.inr
    obtain ⟨⟨status,exec,store,platform⟩,returned,mutation,outcome⟩ := WP.spec_imp_exists operation
    rw [returned,WP.spec_ok]
    have fresh := machine.certified.update mutation
    refine ⟨update _ _ valid mutation,?_,fresh,mutation.metadata.prefix,mutation.extension,?_⟩
    · intro success
      change status=.Ok () at success
      subst status
      obtain ⟨pc,pending,source,invariant,simulation,ownership,ambient,bounded⟩ := outcome
      have owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source := by
        rw [mutation.ownership_bounds]
        exact ownership _ machine.owned
      let next : EventfulMachine emission allowed M P view code expected :=
        ⟨store,exec,platform,source,pc,pending,invariant,fresh,owned⟩
      exact ⟨[],next,rfl,⟨⟨returned,simulation.eventful,mutation.extension,mutation.metadata.prefix,ambient⟩,by simp [stepHostEvents,silent]⟩⟩
    · intro error failed
      change status=.Err error at failed
      subst status
      obtain ⟨cause,decoded⟩ := outcome
      simp only [stepHostEvents,silent]
      rw [decoded]
      exact cause.eventful_error machine.invariant.typed.typed
theorem recorded_inv_step_or_host
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.RecordingHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (Inv : runtime.store.Store M → Prop)
    (update : ∀before after,Inv before → CumulativeStoreMutation view code before after → Inv after)
    {expected : List valtype} (machine : EventfulMachine emission allowed M P view code expected)
    (valid : Inv machine.store)
    (active : 0 < machine.exec.frames.length)
 :
    StructuredHostSite emission allowed view code machine.exec machine.store expected machine.pc machine.pending machine.source ∨
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      Inv out.2.2.1 ∧
      (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        RecordedEventfulTransition memory hooks floats allocator machine events next) ∧
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix machine.store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error →
        EventfulInvocationError (Abs.decode machine.source) (stepHostEvents machine.exec machine.store out)
          (Store.decodeStore view code out.2.2.1) machine.source.ambient error ⦄ := by
  cases selected : hostStepAddress machine.exec machine.store with
  | none =>
    exact recorded_inv_silent_or_host language memory hooks floats allocator correct allocation interrupts view laws code Inv update machine valid active selected
  | some address =>
    exact Or.inl (recording_host_site language view code machine.exec machine.store machine.source expected machine.pc machine.pending
      machine.invariant.storeEq machine.certified.shape machine.owned.values machine.invariant active address selected)
end Exec.Theorems
