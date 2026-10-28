import Exec.Store.Initialization.InitializerMetadataCertificates
import Exec.Store.Preparation.StagingTypeBindings

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TypeEntries.issued {M : Type} {store : runtime.store.Store M} {source addresses}
    (entries : TypeEntries store source addresses) :
    ∀ address ∈ addresses, address.val < store.types.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < source.length := by rw [entries.length_eq]; exact bound
  have found := entries.get sourceBound bound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

theorem ElementTypeMap.issued {M : Type} {store : runtime.store.Store M} {source addresses}
    (entries : ElementTypeMap store source addresses) :
    ∀ address ∈ addresses, address.val < store.elems.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < source.length := by rw [entries.length_eq]; exact bound
  obtain ⟨segment, found, typed⟩ := entries.get sourceBound bound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

theorem TableTypeMap.issued {M : Type} {store : runtime.store.Store M} {source addresses}
    (entries : TableTypeMap store source addresses) :
    ∀ address ∈ addresses, address.index.val < store.tables.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < source.length := by rw [entries.length_eq]; exact bound
  obtain ⟨table, found, typed⟩ := entries.get sourceBound bound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

theorem function_table_addresses {M : Type} {store : runtime.store.Store M} {inst types}
    (table : Interp.FunctionTable store inst types) :
    ∀ address ∈ inst.funcs.val, address.store = store.id ∧ address.index.val < store.funcs.length := by
  intro address member
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < types.length := by rw [← table.length_eq]; exact bound
  obtain ⟨owner, function, signature, found, typed, decoded⟩ := table.get bound sourceBound
  simp only [List.get_eq_getElem, same] at owner found
  exact ⟨owner, (List.getElem?_eq_some_iff.mp found).1⟩

/-- Exact type/signature tables and issued address maps assemble the structural
instance invariant. Every premise is a finite source count or concrete lookup. -/
theorem instance_shape_of_maps {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (types : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (functions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = inst.module.module.env.global_types.length)
    (globalAddresses : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (elements : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val)
    (dataCount : inst.datas.length = inst.module.module.tail.data.length)
    (dataAddresses : ∀ address ∈ inst.datas.val, address.val < store.datas.length) :
    InstanceShape store inst := by
  refine ⟨types.length_eq.symm, ?_, tables.length_eq.symm, memoryCount, globalCount,
    elements.length_eq.symm, dataCount, types.issued, function_table_addresses functions,
    ?_, memoryAddresses, globalAddresses, elements.issued, dataAddresses⟩
  · simpa only [List.length_map] using functions.length_eq
  · intro address member
    exact ⟨tableOwners address member, tables.issued address member⟩

end Itasca.Runtime.Store
