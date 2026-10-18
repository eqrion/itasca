import Exec.Theorems.Composition.Certified.CertifiedSupported
import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Store.Initialization.SegmentAccounting
namespace Exec.Theorems
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The actual store constructor establishes all static cumulative certificates.
The nonzero identity is supplied by the embedding's identity issuer. -/
theorem new_certified_supported {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (id : Usize) (limits : runtime.store.StoreLimits) (identity : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits
      ⦃ store => CertifiedSupportedStore emission allowed view code store ∧ Store.SegmentAccounting store ⦄ := by
  have shape := Store.new_shape memory view id limits identity
  have accounted := Store.new_segment_accounting memory id limits
  simp only [runtime.store.Store.with_identity, WP.spec_ok] at shape accounted ⊢
  refine ⟨⟨shape, ?_, ?_, ?_, ?_, ?_⟩, accounted⟩
  · simp [Store.StoreSyntax]
  · simp [Interp.CoreFunctionsTyped]
  · simp [Abs.FunctionsSupported, Store.decodeStore]
  · simp [Interp.StructuredMachine.CompiledFunctions]
  · constructor <;> simp [alloc.vec.Vec.new]
/-- Complete-profile specialization of the actual empty-store constructor. -/
theorem new_certified_executable {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (id : Usize) (limits : runtime.store.StoreLimits) (identity : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits
      ⦃ store => CertifiedExecutableStore view code store ∧ Store.SegmentAccounting store ⦄ :=
  new_certified_supported memory view code id limits identity
end Exec.Theorems
