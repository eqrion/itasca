import Exec.Interp.FloatCore.Total
import Exec.Theorems.Composition.FloatCore.FloatCoreMutationCertified
import Exec.Theorems.Composition.Core.CoreHostFree
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

theorem step_float_core_certified {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (certified : CertifiedFloatCoreStore view code store)
    (owned : Abs.Ownership.CoreOwned (Store.ownershipBounds store) source)
    (invariant : FloatCoreExecution view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    CoreHostBoundary exec store ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CertifiedFloatCoreStore view code out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      Store.ownershipBounds out.2.2.1 = Store.ownershipBounds store ∧
      FloatCoreOutcome allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
  have small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32 := by
    intro object member ty
    have shape := certified.shape.globals object member
    rcases ty with ty | ty <;> simp only [Store.GlobalShape,ty] at shape <;> exact shape.1
  rcases step_float_core memory hooks floats allocator correct allocation interrupts view laws code exec store platform source expected pc pending
    invariant.storeEq certified.compiled certified.typed small invariant active with host | operation
  · exact Or.inl host
  · apply Or.inr
    apply WP.spec_mono operation
    intro out outcome
    obtain ⟨fresh,extended,bounds⟩ := float_core_mutation_certified view code store out.2.2.1 source certified owned outcome.1
    exact ⟨fresh,extended,bounds,outcome⟩

theorem step_float_core_host_free {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool)
    (certified : CertifiedFloatCoreStore view code store) (hostFree : CoreHostFree store)
    (owned : Abs.Ownership.CoreOwned (Store.ownershipBounds store) source)
    (invariant : FloatCoreExecution view code store exec source expected pc pending)
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CertifiedFloatCoreStore view code out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      Store.ownershipBounds out.2.2.1 = Store.ownershipBounds store ∧
      CoreHostFree out.2.2.1 ∧
      FloatCoreOutcome allocator hooks view code exec store platform expected U32.max pc pending source out ⦄ := by
  rcases step_float_core_certified memory hooks floats allocator correct allocation interrupts view laws code exec store platform source expected pc pending
    certified owned invariant active with host | operation
  · exact False.elim (hostFree.no_boundary exec host)
  · apply WP.spec_mono operation
    intro out effect
    exact ⟨effect.1,effect.2.1,effect.2.2.1,hostFree.mutation effect.2.2.2.1,effect.2.2.2⟩
end Exec.Theorems
