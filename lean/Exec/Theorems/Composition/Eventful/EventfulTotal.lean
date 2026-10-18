import Exec.Theorems.Composition.Eventful.EventfulNonhostStep
import Exec.Theorems.Host.HostSiteEventful
import Exec.Theorems.Composition.Eventful.EventfulLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- All supported active dispatches, including direct and indirect host calls,
return normally and construct exact eventful edges on success. The additional
raw callback retention and issuance hypotheses are explicit; they are not
claimed to follow from the current source-only `HostSound` contract. -/
theorem eventful_step_total
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
    (sound : Platform.HostSound hooks (CertifiedSupportedStore emission allowed view code) (Store.decodeStore view code))
    (preserve : ∀ store, CertifiedSupportedStore emission allowed view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, CertifiedSupportedStore emission allowed view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, CertifiedSupportedStore emission allowed view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (expected : List valtype) :
    EventfulStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected := by
  intro machine active
  rcases eventful_step_or_host language memory hooks floats allocator correct allocation interrupts view laws code machine active with site | ordinary
  · obtain ⟨out,actual,result⟩ := WP.spec_imp_exists (site.eventful_success memory hooks floats allocator allocation interrupts view code sound
      machine.exec machine.store machine.platform machine.certified (preserve _ machine.certified)
      (externs _ machine.certified) (issued _ machine.certified) machine.invariant.typed.typed)
    rw [actual,WP.spec_ok]
    intro success
    obtain ⟨events,next,equal,simulation,extension,metadata,ambient⟩ := result success
    refine ⟨events,next,equal,?_,simulation,extension,metadata,ambient⟩
    exact actual.trans (congrArg Result.ok equal)
  · apply WP.spec_mono ordinary
    intro out result success
    obtain ⟨next,equal,edge⟩ := result.2.1 success
    exact ⟨[],next,equal,edge⟩
end Exec.Theorems
