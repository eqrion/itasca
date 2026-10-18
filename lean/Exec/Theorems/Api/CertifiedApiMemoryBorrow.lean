import Exec.Theorems.Api.CertifiedApiMemoryWrite
namespace Exec.Theorems.CertifiedApi
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Issued mutable-memory access either rejects a foreign identity with an
unchanged backward store, or accepts a same-length byte replacement preserving
the full API invariant. The embedding cannot change a borrowed slice's length. -/
theorem memory_write_issued_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (address : runtime.MemoryAddr)
    (issued : address.store = store.id → address.index.val < store.memories.length) :
    runtime.store.Store.memory_mut memory store address ⦃ answer =>
      (address.store ≠ store.id ∧ answer.1 = .Err .WrongStore ∧ ∀ reply, answer.2 reply = store) ∨
      (address.store = store.id ∧ ∃ initial, answer.1 = .Ok initial ∧
        ∀ bytes : Slice U8, bytes.length = initial.length →
          CertifiedApiStore emission allowed view code (answer.2 (.Ok bytes)) ∧
          Store.FunctionCapacities code (answer.2 (.Ok bytes)) ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code (answer.2 (.Ok bytes)))) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (memory_write_certified memory view laws code store certified capacities index bound)
      rintro answer ⟨read,back⟩
      exact Or.inr ⟨rfl,_,read,back⟩
  · simp [runtime.store.Store.memory_mut,owner]
end Exec.Theorems.CertifiedApi
