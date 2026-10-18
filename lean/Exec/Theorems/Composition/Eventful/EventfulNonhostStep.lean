import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Composition.Supported.SupportedHostDispatch
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Ordinary dispatches in a store containing hosts construct exact eventful
history edges. The remaining alternative is an explicit host-call boundary,
not a host-free premise over the whole store. -/
theorem eventful_step_or_host
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
    {expected : List valtype} (machine : EventfulMachine emission allowed M P view code expected)
    (active : 0 < machine.exec.frames.length) :
    StructuredHostSite emission allowed view code machine.exec machine.store expected machine.pc machine.pending machine.source ∨
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      (out.1=.Ok () → ∃ next : EventfulMachine emission allowed M P view code expected,
        out=(.Ok (),next.exec,next.store,next.platform) ∧
        EventfulTransition memory hooks floats allocator machine [] next) ∧
      (∀ error, out.1=.Err error →
        SupportedStepOutcome emission allowed allocator hooks view code machine.exec machine.store machine.platform
          expected U32.max machine.pc machine.pending machine.source out) ⦄ := by
  rcases step_supported_host_site language memory hooks floats allocator correct allocation interrupts view laws code
    machine.exec machine.store machine.platform machine.source expected machine.pc machine.pending
    machine.invariant.storeEq machine.certified.shape machine.certified.storeSyntax machine.certified.segmentBounds
    machine.certified.compiled machine.certified.typed machine.owned machine.invariant active with host | operation
  · exact Or.inl host
  · apply Or.inr
    obtain ⟨⟨status,exec,store,platform⟩,returned,mutation,outcome⟩ := WP.spec_imp_exists operation
    rw [returned,WP.spec_ok]
    have fresh := machine.certified.update mutation
    refine ⟨fresh,?_,fun _ _ => ⟨mutation,outcome⟩⟩
    intro success
    change status=.Ok () at success
    subst status
    obtain ⟨pc,pending,source,invariant,simulation,ownership,ambient,bounded⟩ := outcome
    have owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source := by
      rw [mutation.ownership_bounds]
      exact ownership _ machine.owned
    let next : EventfulMachine emission allowed M P view code expected :=
      ⟨store,exec,platform,source,pc,pending,invariant,fresh,owned⟩
    exact ⟨next,rfl,returned,simulation.eventful,mutation.extension,mutation.metadata.prefix,ambient⟩
end Exec.Theorems
