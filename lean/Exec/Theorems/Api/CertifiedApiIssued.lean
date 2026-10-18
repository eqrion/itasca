import Exec.Theorems.Api.CertifiedApiGrowth
import Exec.Theorems.Api.CertifiedApiWrites
import Exec.Theorems.Api.CertifiedApiDefinitions
import Exec.Store.Invariant.IssuedValues
namespace Exec.Theorems.CertifiedApi
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Every issued address/value combination preserves the current certificate,
including foreign identities, wrong types, and rejected element bounds. -/
theorem global_write_issued_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (address : runtime.GlobalAddr)  (value : runtime.Value)
    (issuedAddress : address.store = store.id → address.index.val < store.globals.length)
    (issuedValue : Store.IssuedValue store value) :
    runtime.store.Store.set_global memory store address value ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  have unchanged := And.intro certified (And.intro capacities (Spec.extend_store_refl _
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)))
  by_cases same : address.store = store.id
  · have inBounds := issuedAddress same
    cases address with
    | mk owner position =>
      dsimp only at same inBounds
      subst owner
      rcases Store.issued_value_owned_or_foreign store value issuedValue with owned | foreign
      · exact global_write_any_certified memory view code store certified capacities position value inBounds owned
      · rw [Store.global_write_foreign_value memory store position value foreign]
        simpa only [WP.spec_ok] using unchanged
  · rw [Store.set_global_wrong_store memory store address value same]
    simpa only [WP.spec_ok] using unchanged

/-- Every issued address/value combination preserves the current certificate,
including foreign identities, wrong types, and rejected element bounds. -/
theorem table_write_issued_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
    (issuedAddress : address.store = store.id → address.index.val < store.tables.length)
    (issuedValue : Store.IssuedValue store value) :
    runtime.store.Store.set_table memory store address index value ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  have unchanged := And.intro certified (And.intro capacities (Spec.extend_store_refl _
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)))
  by_cases same : address.store = store.id
  · have inBounds := issuedAddress same
    cases address with
    | mk owner position =>
      dsimp only at same inBounds
      subst owner
      rcases Store.issued_value_owned_or_foreign store value issuedValue with owned | foreign
      · exact table_write_any_certified memory view code store certified capacities position index value inBounds owned
      · rw [Store.table_write_foreign_value memory store position index value foreign]
        simpa only [WP.spec_ok] using unchanged
  · rw [Store.set_table_wrong_store memory store address index value same]
    simpa only [WP.spec_ok] using unchanged

/-- Every issued address/value combination preserves the current certificate,
including foreign identities, wrong types, and rejected element bounds. -/
theorem table_grow_issued_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (address : runtime.TableAddr) (delta : U32) (value : runtime.Value)
    (issuedAddress : address.store = store.id → address.index.val < store.tables.length)
    (issuedValue : Store.IssuedValue store value) :
    runtime.store.Store.grow_table_with memory allocator store address delta value ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  have unchanged := And.intro certified (And.intro capacities (Spec.extend_store_refl _
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)))
  by_cases same : address.store = store.id
  · have inBounds := issuedAddress same
    cases address with
    | mk owner position =>
      dsimp only at same inBounds
      subst owner
      rcases Store.issued_value_owned_or_foreign store value issuedValue with owned | foreign
      · exact table_grow_any_certified memory allocator allocation view code store certified capacities position delta value inBounds owned
      · rw [Store.table_grow_foreign_value memory allocator store position delta value foreign]
        simpa only [WP.spec_ok] using unchanged
  · rw [Store.table_grow_wrong_store memory allocator store address delta value same]
    simpa only [WP.spec_ok] using unchanged

/-- The public memory growth theorem also covers issued foreign handles. -/
theorem memory_grow_issued_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (address : runtime.MemoryAddr) (delta : U32)
    (issuedAddress : address.store = store.id → address.index.val < store.memories.length) :
    runtime.store.Store.grow_memory_with memory store address delta ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  by_cases same : address.store = store.id
  · have inBounds := issuedAddress same
    cases address with
    | mk owner position =>
      dsimp only at same inBounds
      subst owner
      exact memory_grow_certified memory view laws code store certified capacities position delta inBounds
  · rw [Store.memory_grow_wrong_store memory store address delta same]
    exact ⟨certified, capacities, Spec.extend_store_refl _
      (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)⟩

/-- Defining a global also preserves certificates for issued foreign values. -/
theorem define_global_issued_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (ty : Itasca.types.GlobalType)
    (value : runtime.Value) (issued : Store.IssuedValue store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  rcases Store.issued_value_owned_or_foreign store value issued with owned | foreign
  · exact define_global_any_certified memory allocator allocation view code store certified capacities ty value owned
  · have bound : Store.objectCount store ≤ Usize.max := by
      have h := certified.shape.object_count_bound
      scalar_tac
    apply WP.spec_mono (Store.define_global_foreign_value memory allocator store ty value bound foreign)
    rintro answer ⟨error, same⟩
    rw [same]
    exact ⟨certified, capacities, Spec.extend_store_refl _
      (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)⟩
end Exec.Theorems.CertifiedApi
