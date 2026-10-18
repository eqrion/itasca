import Exec.Theorems.Composition.Eventful.EventfulTotal
import Exec.Theorems.Host.HostSiteEventfulEffects
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Actual dispatch outcomes retain successful history edges and source error
endpoints, including any store effects committed by a host callback. -/
def EventfulStepOutcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype) : Prop :=
  ∀ machine : EventfulMachine emission allowed M P view code expected, 0<machine.exec.frames.length →
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        EventfulTransition memory hooks floats allocator machine events next) ∧
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      FrameStorePrefix machine.store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code out.2.2.1) ∧
      ∀error,out.1=.Err error → ∃events,
        EventfulInvocationError (Abs.decode machine.source) events
          (Store.decodeStore view code out.2.2.1) machine.source.ambient error ⦄

theorem eventful_step_outcomes
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
    EventfulStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected := by
  intro machine active
  have total := eventful_step_total language memory hooks floats allocator correct allocation interrupts view laws code
    sound preserve externs issued expected machine active
  obtain ⟨out,actual,success⟩ := WP.spec_imp_exists total
  rw [actual,WP.spec_ok]
  refine ⟨success,?_⟩
  rcases eventful_step_or_host language memory hooks floats allocator correct allocation interrupts view laws code machine active with site | ordinary
  · have effects := site.eventful_effects memory hooks floats allocator allocation interrupts view code sound
      machine.exec machine.store machine.platform machine.certified (preserve _ machine.certified)
      (externs _ machine.certified) (issued _ machine.certified) machine.invariant.typed.typed
    simpa only [actual,WP.spec_ok] using effects
  · rw [actual,WP.spec_ok] at ordinary
    refine ⟨ordinary.1,?_,?_,?_⟩
    · cases status : out.1 with
      | Ok unit =>
        cases unit
        obtain ⟨events,next,equal,edge⟩ := success status
        simpa only [equal] using edge.metadata
      | Err error => exact (ordinary.2.2 error status).1.metadata.prefix
    · cases status : out.1 with
      | Ok unit =>
        cases unit
        obtain ⟨events,next,equal,edge⟩ := success status
        simpa only [equal] using edge.extension
      | Err error => exact (ordinary.2.2 error status).1.extension
    · intro error failed
      have outcome := (ordinary.2.2 error failed).2
      simp only [failed] at outcome
      refine ⟨[],?_⟩
      rw [outcome.2]
      exact outcome.1.eventful_error machine.invariant.typed.typed
end Exec.Theorems
