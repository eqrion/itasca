import Exec.Theorems.Api.CertifiedApi
import Exec.Store.Api.MemoryGrowExtension
import Exec.Store.Api.TableGrowExtension
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Invariant.InvalidWrite
namespace Exec.Theorems.CertifiedApi
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Internal memory growth preserves the complete execution certificate and
source capacities, including representation-changing allocation refusals. -/
theorem memory_grow_index_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (index : Usize) (delta : U32) (inBounds : index.val < store.memories.length) :
    runtime.store.Store.grow_memory_index memory store index delta ⦃ result =>
      CertifiedApiStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  obtain ⟨result, returned, shape, sourceSyntax, extension⟩ := WP.spec_imp_exists
    (Store.memory_grow_extends memory view laws code store certified.shape certified.storeSyntax index delta inBounds)
  have effect := Store.memory_grow_effect memory view laws code store index delta inBounds
    (fun m member => (certified.shape.memories m member).length_bound)
    (fun m member => (certified.shape.memories m member).1)
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  rcases effect with ⟨_, _, unchanged | ⟨old, after, lookup, sameView, same⟩⟩ |
    ⟨old, after, count, lookup, bytes, used, limit, pages, maximum, oldPages, same⟩
  · simpa only [unchanged] using And.intro certified (And.intro capacities extension)
  all_goals
    rw [same] at shape extension ⊢
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
      capacities.metadata rfl rfl rfl rfl, extension⟩

/-- Table growth preserves semantic/compiler certificates on every outcome,
including the maximal-size successful zero-growth sentinel case. -/
theorem table_grow_index_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (index : Usize) (delta : U32) (value : U64) (inBounds : index.val < store.tables.length)
    (owned : Store.ReferenceShape store (store.tables.val[index.val]).ty value) :
    runtime.store.Store.grow_table_index memory allocator store index delta value ⦃ result =>
      CertifiedApiStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  obtain ⟨result, returned, shape, sourceSyntax, extension⟩ := WP.spec_imp_exists
    (Store.table_grow_extends memory allocator allocation view code store certified.shape certified.storeSyntax
      index delta value inBounds owned)
  have effect := Store.table_grow_effect memory allocator allocation store index delta value inBounds
    (fun table member => (certified.shape.tables table member).1)
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  rcases effect with ⟨_, unchanged⟩ |
    ⟨old, elements, count, lookup, values, capacity, used, limit, maximum, same⟩
  · simpa only [unchanged] using And.intro certified (And.intro capacities extension)
  · rw [same] at shape extension ⊢
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
      capacities.metadata rfl rfl rfl rfl, extension⟩

/-- Actual public memory growth retains the execution certificate and capacity
ledger and extends the decoded source store. -/
theorem memory_grow_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (index : Usize) (delta : U32) (inBounds : index.val < store.memories.length) :
    runtime.store.Store.grow_memory_with memory store ⟨store.id, index⟩ delta ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step with memory_grow_index_certified memory view laws code store certified capacities index delta inBounds
    as ⟨result, after, certificate, bounds, extension⟩
  exact ⟨certificate, bounds, extension⟩

/-- Public table growth preserves the full current certificate for a typed,
owned fill value and an issued table address. -/
theorem table_grow_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (index : Usize) (delta : U32) (value : runtime.Value)
    (inBounds : index.val < store.tables.length)
    (typed : Store.elementValueType (store.tables.val[index.val]).ty = Interp.rawType value)
    (owned : Store.ValueInStore store value) :
    runtime.store.Store.grow_table_with memory allocator store ⟨store.id, index⟩ delta value ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  unfold runtime.store.Store.grow_table_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [Store.check_value_owned memory store value owned.1]
  simp
  step with Interp.vec_index_given store.tables index store.tables.val[index.val]
    (List.getElem?_eq_getElem inBounds) as ⟨table, found⟩
  subst table
  simp [typed, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  step with Store.encode_reference_shape store value (store.tables.val[index.val]).ty typed owned
    as ⟨lo, hi, canonical⟩
  step with table_grow_index_certified memory allocator allocation view code store certified capacities
    index delta lo inBounds canonical as ⟨result, after, certificate, bounds, extension⟩
  exact ⟨certificate, bounds, extension⟩
/-- A rejected fill type also preserves all execution certificates. -/
theorem table_grow_any_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store)
    (index : Usize) (delta : U32) (value : runtime.Value)
    (inBounds : index.val < store.tables.length) (owned : Store.ValueInStore store value) :
    runtime.store.Store.grow_table_with memory allocator store ⟨store.id, index⟩ delta value ⦃ answer =>
      CertifiedApiStore emission allowed view code answer.2 ∧ Store.FunctionCapacities code answer.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2) ⦄ := by
  by_cases typed : Store.elementValueType (store.tables.val[index.val]).ty = Interp.rawType value
  · exact table_grow_certified memory allocator allocation view code store certified capacities
      index delta value inBounds typed owned
  · apply WP.spec_mono (Store.table_grow_wrong_type memory allocator store index delta value inBounds owned typed)
    intro answer same
    simp only [same]
    exact ⟨certified, capacities, Spec.extend_store_refl _
      (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)⟩
end Exec.Theorems.CertifiedApi
