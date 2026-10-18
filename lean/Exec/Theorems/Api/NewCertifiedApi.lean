import Exec.Theorems.Api.CertifiedApi
import Exec.Theorems.Composition.NewCertifiedSupported
import Exec.Store.Invariant.CapacityHost
namespace Exec.Theorems
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Actual construction establishes the public API invariant and both resource
ledgers, without assuming an already valid store. -/
theorem new_certified_api {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (id : Usize) (limits : runtime.store.StoreLimits) (identity : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store =>
      CertifiedApiStore emission allowed view code store ∧ Store.SegmentAccounting store ∧
      Store.FunctionCapacities code store ⦄ := by
  obtain ⟨store,returned,certified,accounted⟩ := WP.spec_imp_exists
    (new_certified_supported (emission := emission) (allowed := allowed) memory view code id limits identity)
  have exports := Store.new_export_bounds memory id limits
  have capacities := Store.new_function_capacities memory id limits code
  rw [returned,WP.spec_ok] at exports capacities ⊢
  exact ⟨⟨certified,exports⟩,accounted,capacities⟩

theorem new_certified_executable_api {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (id : Usize) (limits : runtime.store.StoreLimits) (identity : 0 < id.val) :
    runtime.store.Store.with_identity memory id limits ⦃ store =>
      CertifiedExecutableApiStore view code store ∧ Store.SegmentAccounting store ∧
      Store.FunctionCapacities code store ⦄ :=
  new_certified_api memory view code id limits identity
end Exec.Theorems
