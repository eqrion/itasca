import Exec.Theorems.Composition.Eventful.EventfulWorldStep
import Exec.Theorems.Composition.Recorded.RecordedNonhostStep
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem world_step_or_host
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
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    {expected : List valtype} (machine : EventfulMachine emission allowed M P view code expected)
    (valid : Inv code machine.store)
    (active : 0 < machine.exec.frames.length)
 :
    StructuredHostSite emission allowed view code machine.exec machine.store expected machine.pc machine.pending machine.source ∨
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform
      ⦃ out => WorldStepResult memory hooks floats allocator Inv ⟨code,machine⟩ out ⦄ := by
  cases selected : hostStepAddress machine.exec machine.store with
  | some address =>
    exact Or.inl (recording_host_site language view code machine.exec machine.store machine.source expected machine.pc machine.pending
      machine.invariant.storeEq machine.certified.shape machine.owned.values machine.invariant active address selected)
  | none =>
    rcases step_supported_host_site language memory hooks floats allocator correct allocation interrupts view laws code
      machine.exec machine.store machine.platform machine.source expected machine.pc machine.pending
      machine.invariant.storeEq machine.certified.shape machine.certified.storeSyntax machine.certified.segmentBounds
      machine.certified.compiled machine.certified.typed machine.owned machine.invariant active with host | operation
    · exact Or.inl host
    · apply Or.inr
      obtain ⟨⟨status,exec,store,platform⟩,returned,mutation,outcome⟩ := WP.spec_imp_exists operation
      rw [returned,WP.spec_ok]
      have fresh := machine.certified.update mutation
      have newValid := update code _ _ valid mutation
      cases status with
      | Ok value =>
        cases value
        obtain ⟨pc,pending,source,invariant,simulation,ownership,ambient,bounded⟩ := outcome
        have owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source := by
          rw [mutation.ownership_bounds]
          exact ownership _ machine.owned
        let next : EventfulMachine emission allowed M P view code expected :=
          ⟨store,exec,platform,source,pc,pending,invariant,fresh,owned⟩
        have edge : EventfulTransition memory hooks floats allocator machine [] next :=
          ⟨returned,simulation.eventful,mutation.extension,mutation.metadata.prefix,ambient⟩
        refine ⟨⟨code,next⟩,newValid,rfl,?_⟩
        simpa only [stepHostEvents,selected] using edge.world
      | Err error =>
        obtain ⟨cause,decoded⟩ := outcome
        refine ⟨code,newValid,fresh,mutation.metadata.prefix,(by intro index inst found fn; rfl),mutation.extension,?_,Or.inl ⟨cause,decoded⟩⟩
        simp only [stepHostEvents,selected]
        rw [decoded]
        exact cause.eventful_error machine.invariant.typed.typed
end Exec.Theorems
