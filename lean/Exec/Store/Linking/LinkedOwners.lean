import Exec.Store.Linking.LinkMaps

namespace Exec.Store
open Aeneas Aeneas.Std

theorem LinkedMaps.tables_owned {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module entries inst}
    (maps : LinkedMaps view store module entries inst) :
    ∀ address ∈ inst.tables.val, address.store = store.id := by
  intro address member
  obtain ⟨index, bound, read⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < (Itasca.ModuleEnv.importedTables entries).length := by
    rw [maps.tables.length_eq]
    exact bound
  have related := maps.tables.get sourceBound bound
  simp only [List.get_eq_getElem, read] at related
  exact related.1

theorem LinkedMaps.memories_owned {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module entries inst}
    (maps : LinkedMaps view store module entries inst) :
    ∀ address ∈ inst.memories.val, address.store = store.id := by
  intro address member
  obtain ⟨index, bound, read⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < (Itasca.ModuleEnv.importedMems entries).length := by
    rw [maps.memories.length_eq]
    exact bound
  have related := maps.memories.get sourceBound bound
  simp only [List.get_eq_getElem, read] at related
  exact related.1

theorem LinkedMaps.globals_owned {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module entries inst}
    (maps : LinkedMaps view store module entries inst) :
    ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length := by
  intro address member
  obtain ⟨index, bound, read⟩ := List.mem_iff_getElem.mp member
  have sourceBound : index < (Itasca.ModuleEnv.importedGlobals entries).length := by
    rw [maps.globals.length_eq]
    exact bound
  have related := maps.globals.get sourceBound bound
  simp only [List.get_eq_getElem, read] at related
  obtain ⟨owner, global, found, typed⟩ := related
  exact ⟨owner, (List.getElem?_eq_some_iff.mp found).1⟩

end Exec.Store
