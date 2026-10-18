import Exec.Theorems.Composition.Eventful.EventfulDispatchCauses
import Exec.Theorems.Composition.Eventful.EventfulCausalNonhost
import Exec.Theorems.Host.HostSiteEventfulInvariant
import Exec.Theorems.Host.HostSiteEventfulCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The actual common dispatcher preserves an auxiliary API invariant. Host
soundness is required only for that invariant; ordinary mutations use its
checked preservation adapter. Source results and errors remain unchanged. -/
theorem eventful_causal_step_outcomes
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
    (certify : ∀s,Inv s → CertifiedSupportedStore emission allowed view code s)
    (update : ∀before after,Inv before → CumulativeStoreMutation view code before after → Inv after)
    (sound : Platform.HostSound hooks Inv (Store.decodeStore view code))
    (preserve : ∀ store, Inv store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, Inv store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, Inv store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (expected : List valtype) :
    EventfulCausalStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv
      (EventfulDispatchCause memory hooks floats allocator) := by
  intro machine valid active
  rcases eventful_causal_step_or_host language memory hooks floats allocator correct allocation interrupts view laws code Inv update machine valid active with site | ordinary
  · obtain ⟨out,actual,result⟩ := WP.spec_imp_exists
      (site.eventful_invariant_success memory hooks floats allocator allocation interrupts view code Inv certify sound
        machine.exec machine.store machine.platform valid (preserve _ valid) (externs _ valid) (issued _ valid) machine.invariant.typed.typed)
    have effects := site.eventful_invariant_causes memory hooks floats allocator allocation interrupts view code Inv certify sound
      machine.exec machine.store machine.platform valid (preserve _ valid) (externs _ valid) (issued _ valid) machine.invariant.typed.typed
    rw [actual,WP.spec_ok] at effects ⊢
    refine ⟨effects.1,?_,effects.2.1,effects.2.2.1,effects.2.2.2.1,?_⟩
    · intro success
      obtain ⟨events,next,equal,simulation,extension,metadata,ambient⟩ := result.2 success
      refine ⟨events,next,equal,?_,simulation,extension,metadata,ambient⟩
      exact actual.trans (congrArg Result.ok equal)
    · intro error failed
      obtain ⟨events,source,cause⟩ := effects.2.2.2.2 error failed
      exact ⟨events,source,Or.inr cause⟩
  · apply WP.spec_mono ordinary
    intro out result
    refine ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2.1,?_⟩
    intro error failed
    obtain ⟨events,source,cause⟩ := result.2.2.2.2.2 error failed
    exact ⟨events,source,Or.inl cause⟩
end Exec.Theorems
