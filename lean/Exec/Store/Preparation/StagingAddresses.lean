import Exec.Store.Api.TableStaging
import Exec.Store.Api.MemoryStaging
import Exec.Store.Api.GlobalResultEffect
import Exec.Store.Initialization.DataResultEffect

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TableStageEffect.owners {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    (owners : ∀ address ∈ inst.tables.val, address.store = store.id) :
    ∀ address ∈ out.2.2.tables.val, address.store = out.2.1.id := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact owners
  · intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact owners address old
    · rfl

theorem MemoryStageEffect.owners {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : MemoryStageEffect view store inst ty out)
    (owners : ∀ address ∈ inst.memories.val, address.store = store.id) :
    ∀ address ∈ out.2.2.memories.val, address.store = out.2.1.id := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact owners
  · intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact owners address old
    · rfl

theorem GlobalStageEffect.addresses {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    (issued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length) :
    ∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact issued
  | appended globals addresses global stored mapped canonical room =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    have size : globals.length = store.globals.length + 1 := by simpa using congrArg List.length stored
    rcases member with old | rfl
    · obtain ⟨owner, previous⟩ := issued address old
      exact ⟨owner, by simp only [size]; omega⟩
    · exact ⟨rfl, by simp [size]⟩

theorem DataStageEffect.addresses {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    (issued : ∀ address ∈ inst.datas.val, address.val < store.datas.length) :
    ∀ address ∈ next.datas.val, address.val < after.datas.length := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact issued
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    have size : datas.length = store.datas.length + 1 := by simpa using congrArg List.length stored
    rcases member with old | rfl
    · have previous := issued address old
      simp only [size]
      omega
    · simp [size]

end Itasca.Runtime.Store
