import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Invariant.FunctionStaging

/-!
Sections, each formerly its own module: StagingAddresses, PreparationResults.
-/

/-! ## StagingAddresses -/

section

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

end

/-! ## PreparationResults -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem type_parts_inj {M : Type} (a b : runtime.store.Store M)
    (s t : core.result.Result Unit runtime.ExecError) (i j : runtime.store.ModuleInst) :
    typeParts a s i = typeParts b t j ↔ a = b ∧ s = t ∧ i = j := by
  cases i; cases j
  simp [typeParts]

/-- Normalize the flattened tuple returned by the actual preparation loops.
The computation and its checked total postcondition remain explicit. -/
theorem preparation_result {M R : Type}
    (parts : runtime.store.Store M → core.result.Result Unit runtime.ExecError → runtime.store.ModuleInst → R)
    (injective : ∀ a b s t i j, parts a s i = parts b t j → a = b ∧ s = t ∧ i = j)
    (computation : Result R) (post : runtime.store.Store M → runtime.store.ModuleInst → core.result.Result Unit runtime.ExecError → Prop)
    (checked : computation ⦃ out => ∃ store inst status, out = parts store status inst ∧ post store inst status ⦄)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (run : computation = .ok (parts store status inst)) : post store inst status := by
  rw [run] at checked
  simp only [WP.spec_ok] at checked
  obtain ⟨after, next, result, eq, property⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := injective _ _ _ _ _ _ eq
  exact property

end Itasca.Runtime.Store

end
