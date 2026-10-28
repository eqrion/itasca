import Itasca.Runtime.Store.Linking.LinkMaps
import Itasca.Runtime.Store.Api.TableStaging
import Itasca.Runtime.Store.Api.MemoryStaging

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev TableBindings {M : Type} (store : runtime.store.Store M)
    (types : List Itasca.types.TableType) (addresses : List runtime.TableAddr) : Prop :=
  List.Forall₂ (ImportedTable store) types addresses

abbrev MemoryBindings {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (types : List Itasca.types.MemType) (addresses : List runtime.MemoryAddr) : Prop :=
  List.Forall₂ (ImportedMemory view store) types addresses

theorem TableBindings.prefix {M : Type} {store after : runtime.store.Store M} {types addresses}
    (matching : TableBindings store types addresses) (identity : after.id = store.id)
    (retained : after.tables.val.take store.tables.length = store.tables.val) :
    TableBindings after types addresses := by
  apply matching.imp
  rintro ty address ⟨owner, table, found, equal, limits⟩
  refine ⟨owner.trans identity.symm, table, ?_, equal, limits⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lookup := congrArg (fun values : List runtime.store.TableInst => values[address.index.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at lookup
  exact lookup.trans found

theorem MemoryBindings.prefix {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M} {types addresses}
    (matching : MemoryBindings view store types addresses) (identity : after.id = store.id)
    (retained : after.memories.val.take store.memories.length = store.memories.val) :
    MemoryBindings view after types addresses := by
  apply matching.imp
  rintro ty address ⟨owner, memory, found, limits⟩
  refine ⟨owner.trans identity.symm, memory, ?_, limits⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lookup := congrArg (fun values : List (runtime.store.MemInst M) => values[address.index.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at lookup
  exact lookup.trans found

theorem TableStageEffect.table_bindings {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    {types : List Itasca.types.TableType} (matching : TableBindings store types inst.tables.val)
    (success : out.1 = .Ok ()) : TableBindings out.2.1 (types ++ [ty]) out.2.2.tables.val := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · simp at success
  · have old := matching.prefix (after := {store with tables, table_elements := count}) rfl (by simp [appended])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    refine .cons ⟨rfl, {elements, ty := ty.elem, maximum := ty.limits.max}, by simp [appended], rfl, ?_⟩ .nil
    refine ⟨by simp [alloc.vec.Vec.length, zeros], ?_⟩
    intro bound found
    exact ⟨bound, found, le_refl _⟩

theorem MemoryStageEffect.memory_bindings {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : MemoryStageEffect view store inst ty out)
    {types : List Itasca.types.MemType} (matching : MemoryBindings view store types inst.memories.val)
    (success : out.1 = .Ok ()) : MemoryBindings view out.2.1 (types ++ [ty]) out.2.2.memories.val := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · simp at success
  · have old := matching.prefix (after := {store with memories, memory_bytes := count}) rfl (by simp [appended])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    refine .cons ⟨rfl, {buf := buffer, maximum := ty.limits.max}, by simp [appended], ?_⟩ .nil
    refine ⟨by simp [Slice.length, zeros], ?_⟩
    intro bound found
    exact ⟨bound, found, le_refl _⟩

end Itasca.Runtime.Store
