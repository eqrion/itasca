import Exec.Theorems.Progress.UniformEventfulFinite
import Exec.Theorems.Composition.Uniform.UniformEventfulNonhost
import Exec.Theorems.Host.HostSiteUniform

namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The actual common dispatcher preserves an auxiliary API invariant. Host
soundness is required only for that invariant; ordinary mutations use its
checked preservation adapter. Source results and errors remain unchanged. -/
theorem uniform_eventful_inv_step_total
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
    UniformEventfulInvStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv := by
  intro machine valid active
  rcases uniform_eventful_inv_step_or_host language memory hooks floats allocator correct allocation interrupts view laws code Inv update machine valid active with site | ordinary
  · obtain ⟨out,actual,result⟩ := WP.spec_imp_exists
      (site.uniform_invariant_success memory hooks floats allocator allocation interrupts view code Inv certify sound
        machine.exec machine.store machine.platform valid (preserve _ valid) (externs _ valid) (issued _ valid) machine.invariant.typed.typed)
    rw [actual,WP.spec_ok]
    refine ⟨result.1,?_⟩
    intro success
    obtain ⟨events,next,equal,simulation,uniform,extension,metadata,ambient⟩ := result.2 success
    exact ⟨events,next,equal,⟨actual.trans (congrArg Result.ok equal),simulation,extension,metadata,ambient⟩,uniform⟩
  · apply WP.spec_mono ordinary
    intro out result
    exact ⟨result.1,result.2.1⟩
end Exec.Theorems
