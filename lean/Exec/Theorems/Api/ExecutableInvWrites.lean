import Exec.Theorems.Api.ExecutableInv
import Exec.Store.Api.GlobalWriteExtension
import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Typing
import Exec.Spec.Mutation
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Invariant.InvalidWrite
namespace Exec.Theorems.ExecutableInv
open Aeneas Aeneas.Std

/-- Public global writes preserve the complete current execution certificate
and source-capacity ledger, and extend the decoded specification store. -/
theorem global_write_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : ExecutableInv view code store)

    (index : Usize) (value : runtime.Value)
    (inBounds : index.val < store.globals.length)
    (mutable : (store.globals.val[index.val]).ty.mutability = .Var)
    (typed : (store.globals.val[index.val]).ty.valtype = Interp.rawType value)
    (owned : Store.ValueInStore store value) :
    runtime.store.Store.set_global memory store ⟨store.id, index⟩ value ⦃ answer =>
      answer.1 = .Ok () ∧ ExecutableInv view code answer.2 ∧
      Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  let capacities := certified.capacities
  obtain ⟨answer, returned, ok, shape, sourceSyntax, extension⟩ := WP.spec_imp_exists
    (Store.global_write_extends memory view code store certified.shape certified.storeSyntax index value
      inBounds mutable typed owned)
  have effect := Store.global_write memory store index value inBounds mutable typed owned.1
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  obtain ⟨words, encoded, represented, same⟩ := effect
  rw [same] at shape extension ⊢
  exact ⟨rfl, certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
    capacities.metadata rfl rfl rfl rfl, extension⟩

/-- Wrong types and immutable destinations preserve the same public invariants
as successful writes, with no mutability or value-type premise. -/
theorem global_write_any_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : ExecutableInv view code store)

    (index : Usize) (value : runtime.Value) (inBounds : index.val < store.globals.length)
    (owned : Store.ValueInStore store value) :
    runtime.store.Store.set_global memory store ⟨store.id, index⟩ value ⦃ answer =>
      ExecutableInv view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  let capacities := certified.capacities
  have unchanged : ExecutableInv view code store ∧ Store.FunctionCapacities code store ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code store) :=
    ⟨certified, capacities, Spec.extend_store_refl _
      (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)⟩
  by_cases mutable : (store.globals.val[index.val]).ty.mutability = .Var
  · by_cases typed : (store.globals.val[index.val]).ty.valtype = Interp.rawType value
    · exact WP.spec_mono (global_write_certified memory view code store certified index value
        inBounds mutable typed owned) (fun _ post => post.2)
    · apply WP.spec_mono (Store.global_write_rejected memory store index value inBounds owned (Or.inr typed))
      intro answer same
      simpa only [same] using unchanged
  · apply WP.spec_mono (Store.global_write_rejected memory store index value inBounds owned (Or.inl mutable))
    intro answer same
    simpa only [same] using unchanged

end Exec.Theorems.ExecutableInv
