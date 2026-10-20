import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Theorems.Composition.Supported.SupportedChosenTotal
import Exec.Theorems.Composition.Core.CoreHostFree
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
theorem step_supported_chosen_host_free {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    (occurrence : Nat)
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
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (certified : CertifiedSupportedStore emission allowed view code store) (hostFree : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source)
    (invariant : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CertifiedSupportedStore emission allowed view code out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      Store.ownershipBounds out.2.2.1 = Store.ownershipBounds store ∧
      CoreHostFree out.2.2.1 ∧
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
  apply WP.spec_mono (step_supported_chosen admissible numericChoice vector occurrence language memory hooks floats allocator correct allocation interrupts view laws code compatible exec store platform source expected pc pending
    invariant.storeEq certified.shape certified.storeSyntax certified.segmentBounds certified.compiled certified.typed hostFree owned invariant active)
  intro out outcome
  exact ⟨certified.update outcome.1,outcome.1.extension,outcome.1.ownership_bounds,
    hostFree.frame_metadata outcome.1.metadata,outcome⟩
end Exec.Theorems
