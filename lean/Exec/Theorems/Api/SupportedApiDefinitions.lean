import Exec.Theorems.Composition.Certified.CertifiedSupportedContent
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Api.DefineTable
import Exec.Store.Invariant.InvalidWrite
import Exec.Store.Invariant.ObjectExtension
namespace Exec.Theorems.SupportedApi
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Appending an external identity leaves the decoded WebAssembly store intact
and retains execution and source-capacity certificates. -/
theorem define_extern_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (identity : U64) :
    runtime.store.Store.define_extern_with memory allocator store identity ⦃ result =>
      CertifiedSupportedStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := certified.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, shape⟩ := WP.spec_imp_exists
    (Store.define_extern_preserves_shape memory allocator allocation view store certified.shape identity)
  have effect := Store.define_extern_effect memory allocator allocation store identity bound
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  have unchanged := Spec.extend_store_refl _
    (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)
  rcases effect with ⟨error, same⟩ | ⟨externs, values, room, same⟩
  · simpa only [same] using And.intro certified (And.intro capacities unchanged)
  · rw [same] at shape ⊢
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape unchanged,
      capacities.metadata rfl rfl rfl rfl, unchanged⟩

/-- A new owned global extends the decoded store while preserving every
existing compiled function and its source-capacity environment. -/
theorem define_global_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (ty : Itasca.types.GlobalType)
    (value : runtime.Value) (typed : ty.valtype = Interp.rawType value)
    (owned : Store.ValueInStore store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ result =>
      CertifiedSupportedStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := certified.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, shape⟩ := WP.spec_imp_exists
    (Store.define_global_preserves_shape memory allocator allocation view store certified.shape ty value typed owned)
  have effect := Store.define_global_effect memory allocator allocation store ty value bound typed owned
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  have oldWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  rcases effect with ⟨error, same⟩ | ⟨globals, words, encoded, values, room, same⟩
  · simpa only [same] using And.intro certified
      (And.intro capacities (Spec.extend_store_refl _ oldWf))
  · rw [same] at shape ⊢
    have sourceSyntax : Store.StoreSyntax code {store with globals} := certified.storeSyntax
    have newWf := Store.decodeStore_wf view code {store with globals} shape sourceSyntax
    have decoded : Store.decodeStore view code {store with globals} =
        {Store.decodeStore view code store with GLOBALS := (Store.decodeStore view code store).GLOBALS ++
          [Store.decodeGlobal {ty, lo := words.1, hi := words.2}]} := by
      simp only [Store.decodeStore, values, List.map_append, List.map_cons, List.map_nil]
      rfl
    have extension : Extend_store (Store.decodeStore view code store)
        (Store.decodeStore view code {store with globals}) := by
      rw [decoded] at newWf ⊢
      simpa only [List.append_nil] using Spec.extend_store_append
        (Store.decodeStore view code store) ⟨[], [Store.decodeGlobal {ty, lo := words.1, hi := words.2}], [], [], [], []⟩
        oldWf (by simpa only [List.append_nil] using newWf)
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
      capacities.metadata rfl rfl rfl rfl, extension⟩

/-- Defining a memory preserves the current certified store on success and
rejection, and appends exactly one source object on success. -/
theorem define_memory_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (ty : Itasca.types.MemType) (buffer : M) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ result =>
      CertifiedSupportedStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := certified.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, shape⟩ := WP.spec_imp_exists
    (Store.define_memory_preserves_shape memory allocator allocation view laws store certified.shape ty buffer)
  have effect := Store.define_memory_effect memory allocator allocation view laws store ty buffer bound
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  have oldWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  rcases effect with ⟨error, same⟩ | ⟨memories, count, values, limits, size, room, total, limit, same⟩
  · simpa only [same] using And.intro certified
      (And.intro capacities (Spec.extend_store_refl _ oldWf))
  · rw [same] at shape ⊢
    have sourceSyntax : Store.StoreSyntax code {store with memories, memory_bytes := count} := certified.storeSyntax
    have newWf := Store.decodeStore_wf view code {store with memories, memory_bytes := count} shape sourceSyntax
    have decoded : Store.decodeStore view code {store with memories, memory_bytes := count} =
        {Store.decodeStore view code store with MEMS := (Store.decodeStore view code store).MEMS ++
          [Store.decodeMemory view {buf := buffer, maximum := ty.limits.max}]} := by
      simp only [Store.decodeStore, values, List.map_append, List.map_cons, List.map_nil]
      rfl
    have extension : Extend_store (Store.decodeStore view code store)
        (Store.decodeStore view code {store with memories, memory_bytes := count}) := by
      rw [decoded] at newWf ⊢
      simpa only [List.append_nil] using Spec.extend_store_append
        (Store.decodeStore view code store) ⟨[], [], [], [Store.decodeMemory view {buf := buffer, maximum := ty.limits.max}], [], []⟩
        oldWf (by simpa only [List.append_nil] using newWf)
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
      capacities.metadata rfl rfl rfl rfl, extension⟩

/-- Defining a table preserves the current certified store on success and
rejection, and appends exactly one source object on success. -/
theorem define_table_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (ty : Itasca.types.TableType) :
    runtime.store.Store.define_table_with memory allocator store ty ⦃ result =>
      CertifiedSupportedStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := certified.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, shape⟩ := WP.spec_imp_exists
    (Store.define_table_preserves_shape memory allocator allocation view store certified.shape ty)
  have effect := Store.define_table_effect memory allocator allocation store ty bound
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  have oldWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  rcases effect with ⟨error, same⟩ | ⟨tables, elements, count, contents, values, limits, room, total, limit, same⟩
  · simpa only [same] using And.intro certified
      (And.intro capacities (Spec.extend_store_refl _ oldWf))
  · rw [same] at shape ⊢
    have sourceSyntax : Store.StoreSyntax code {store with tables, table_elements := count} := certified.storeSyntax
    have newWf := Store.decodeStore_wf view code {store with tables, table_elements := count} shape sourceSyntax
    have decoded : Store.decodeStore view code {store with tables, table_elements := count} =
        {Store.decodeStore view code store with TABLES := (Store.decodeStore view code store).TABLES ++
          [Store.decodeTable {elements, ty := ty.elem, maximum := ty.limits.max}]} := by
      simp only [Store.decodeStore, values, List.map_append, List.map_cons, List.map_nil]
      rfl
    have extension : Extend_store (Store.decodeStore view code store)
        (Store.decodeStore view code {store with tables, table_elements := count}) := by
      rw [decoded] at newWf ⊢
      simpa only [List.append_nil] using Spec.extend_store_append
        (Store.decodeStore view code store) ⟨[], [], [Store.decodeTable {elements, ty := ty.elem, maximum := ty.limits.max}], [], [], []⟩
        oldWf (by simpa only [List.append_nil] using newWf)
    exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,
      capacities.metadata rfl rfl rfl rfl, extension⟩

/-- Global definitions retain certificates even when the initializer type is
rejected; ownership and issued-reference bounds remain explicit. -/
theorem define_global_any_certified {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedSupportedStore emission allowed view code store)
    (capacities : Store.FunctionCapacities code store) (ty : Itasca.types.GlobalType)
    (value : runtime.Value) (owned : Store.ValueInStore store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ result =>
      CertifiedSupportedStore emission allowed view code result.2 ∧ Store.FunctionCapacities code result.2 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code result.2) ⦄ := by
  by_cases typed : ty.valtype = Interp.rawType value
  · exact define_global_certified memory allocator allocation view code store certified capacities ty value typed owned
  · have bound : Store.objectCount store ≤ Usize.max := by
      have h := certified.shape.object_count_bound
      scalar_tac
    apply WP.spec_mono (Store.define_global_wrong_type memory allocator store ty value bound owned typed)
    intro result same
    rw [same]
    exact ⟨certified, capacities, Spec.extend_store_refl _
      (Store.decodeStore_wf view code store certified.shape certified.storeSyntax)⟩
end Exec.Theorems.SupportedApi
