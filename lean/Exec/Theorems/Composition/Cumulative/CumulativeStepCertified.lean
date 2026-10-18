import Exec.Theorems.Composition.Cumulative.CumulativeTotal
import Exec.Theorems.Composition.Core.CoreHostFree
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem step_cumulative_host_free {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (certified : CertifiedCumulativeStore view code store) (hostFree : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source)
    (invariant : Cumulative.Execution view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CertifiedCumulativeStore view code out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      Store.ownershipBounds out.2.2.1 = Store.ownershipBounds store ∧
      CoreHostFree out.2.2.1 ∧
      CumulativeStepOutcome allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
  apply WP.spec_mono (step_cumulative memory hooks floats allocator correct allocation interrupts view laws code exec store platform source expected pc pending
    invariant.storeEq certified hostFree owned invariant active)
  intro out outcome
  exact ⟨certified.update outcome.1,outcome.1.extension,outcome.1.ownership_bounds,
    hostFree.frame_metadata outcome.1.metadata,outcome⟩
end Exec.Theorems
