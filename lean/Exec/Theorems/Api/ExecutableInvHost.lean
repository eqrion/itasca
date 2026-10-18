import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems
open Aeneas Aeneas.Std
namespace ExecutableInv
/-- The public host-definition operation preserves the complete static store
certificate and canonical frame-capacity ledger on success and rejection. -/
theorem define_host_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : ExecutableInv view code store)
 (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator store ty identity ⦃ result =>
      ExecutableInv view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  let capacities := certified.capacities
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := certified.shape.object_count_bound
    scalar_tac
  obtain ⟨result,returned,shape⟩ := WP.spec_imp_exists
    (Store.define_host_preserves_shape memory allocator allocation view store certified.shape ty identity)
  have effect := Store.define_host_effect memory allocator allocation store bound ty identity
  have ledger := Store.define_host_capacities memory allocator allocation view store certified.shape code capacities ty identity
  rw [returned,WP.spec_ok] at effect ledger ⊢
  have fresh := certified.host_definition shape effect ledger
  exact ⟨fresh.1,ledger,fresh.2⟩
end ExecutableInv
end Exec.Theorems
