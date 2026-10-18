import Exec.Theorems.Composition.Certified.CertifiedCumulative
import Exec.Store.Initialization.SegmentAccounting
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- The actual store constructor establishes all static cumulative certificates.
The nonzero identity is supplied by the embedding's identity issuer. -/
theorem new_certified_cumulative {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (id : Usize) (limits : runtime.store.StoreLimits) (identity : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits
      ⦃ store => CertifiedCumulativeStore view code store ∧ Store.SegmentAccounting store ⦄ := by
  have shape := Store.new_shape memory view id limits identity
  have accounted := Store.new_segment_accounting memory id limits
  simp only [runtime.store.Store.with_identity, WP.spec_ok] at shape accounted ⊢
  refine ⟨⟨shape, ?_, ?_, ?_, ?_, ?_⟩, accounted⟩
  · simp [Store.StoreSyntax]
  · simp [Interp.CoreFunctionsTyped]
  · simp [Abs.CumulativeFunctions, Store.decodeStore]
  · simp [Interp.CumulativeCompiledFunctions]
  · constructor <;> simp [alloc.vec.Vec.new]
end Exec.Theorems
