import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Initialization.ElementTypedEffect
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Preparation.PreparationResults
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: AddressOrder, AllocatedMemoryLoop.
-/

/-! ## AddressOrder -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Addresses issued by append-only preparation, in their actual source order. -/
def AddressOrder (start : Nat) (initial : List Nat) (total : Nat) (addresses : List Nat) : Prop :=
  ∃ count, total = start + count ∧ addresses = initial ++ List.range' start count

theorem AddressOrder.refl (start : Nat) (initial : List Nat) : AddressOrder start initial start initial :=
  ⟨0, by simp, by simp⟩

theorem AddressOrder.append {start total : Nat} {initial addresses : List Nat}
    (ordered : AddressOrder start initial total addresses) :
    AddressOrder start initial (total + 1) (addresses ++ [total]) := by
  obtain ⟨count, rfl, rfl⟩ := ordered
  refine ⟨count + 1, by omega, ?_⟩
  simp only [List.range'_concat, Nat.one_mul, List.append_assoc]

theorem AddressOrder.complete {start total count : Nat} {initial addresses : List Nat}
    (ordered : AddressOrder start initial total addresses)
    (lengths : addresses.length = initial.length + count) :
    total = start + count ∧ addresses = initial ++ List.range' start count := by
  obtain ⟨actual, totalEq, values⟩ := ordered
  have same : actual = count := by simp only [values, List.length_append, List.length_range'] at lengths; omega
  simpa only [same] using And.intro totalEq values

theorem FunctionStageEffect.address_order {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out} {start initial}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (ordered : AddressOrder start initial store.funcs.length (inst.funcs.val.map fun address => address.index.val)) :
    AddressOrder start initial out.2.1.funcs.length (out.2.2.funcs.val.map fun address => address.index.val) := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, stored, mapped, capacity, rfl⟩
  · exact ordered
  · simpa [stored, mapped] using ordered.append

theorem GlobalStageEffect.address_order {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {start initial}
    (effect : GlobalStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (ordered : AddressOrder start initial store.globals.length (inst.globals.val.map (fun address => address.index.val))) :
    AddressOrder start initial after.globals.length (next.globals.val.map (fun address => address.index.val)) := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using ordered
  | appended globals addresses global stored mapped canonical room =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    simpa [stored, mapped] using ordered.append

theorem ElementStageEffect.address_order {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {start initial}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (ordered : AddressOrder start initial store.elems.length (inst.elems.val.map (UScalar.val))) :
    AddressOrder start initial after.elems.length (next.elems.val.map (UScalar.val)) := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using ordered
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    simpa [stored, mapped] using ordered.append

theorem DataStageEffect.address_order {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {instIndex : Usize} {start initial}
    (effect : DataStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (ordered : AddressOrder start initial store.datas.length (inst.datas.val.map (UScalar.val))) :
    AddressOrder start initial after.datas.length (next.datas.val.map (UScalar.val)) := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using ordered
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    simpa [stored, mapped] using ordered.append

end Itasca.Runtime.Store

end

/-! ## AllocatedMemoryLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual memory allocation loop establishes complete issued memory maps,
while retaining all old store objects and all other provisional maps. -/
theorem memory_allocated_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.mem_types.val.length)
    (changed : store = {before with memories := store.memories, memory_bytes := store.memory_bytes})
    (instChanged : inst = {seed with memories := inst.memories})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length)
    (owners : ∀ address ∈ inst.memories.val, address.store = store.id)
    (count : inst.memories.length = start.val)
    :
    runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with memories := after.memories, memory_bytes := after.memory_bytes} ∧ next = {seed with memories := next.memories} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (∀ address ∈ next.memories.val, address.index.val < after.memories.length) ∧
        (∀ address ∈ next.memories.val, address.store = after.id) ∧
        (status = .Ok () → next.memories.length = seed.module.module.env.mem_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.mem_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop6
  apply loop.spec_decr_nat (fun state => seed.module.module.env.mem_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with memories := state.1.memories, memory_bytes := state.1.memory_bytes} ∧
      state.2.2.2 = {seed with memories := state.2.2.2.memories} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧
      (∀ address ∈ state.2.2.2.memories.val, address.index.val < state.1.memories.length) ∧
      (∀ address ∈ state.2.2.2.memories.val, address.store = state.1.id) ∧
      state.2.2.1.val ≤ seed.module.module.env.mem_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.memories.length = state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentAllocated currentIssued currentOwners indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop6.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.mem_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.mem_types.val.length := by simpa only [source] using within
        have room : currentInst.memories.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_memory_effect memory allocator law view laws current currentInst index
          actualBound bound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with memories := after.memories, memory_bytes := after.memory_bytes} := by
          calc
            after = {current with memories := after.memories, memory_bytes := after.memory_bytes} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with memories := nextInst.memories} := by
          calc
            nextInst = {currentInst with memories := nextInst.memories} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.allocated currentAllocated,
          effect.issued currentIssued, effect.owners currentOwners, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.mem_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, allocated, issued, owners, startBound, fun _ => count⟩

end Itasca.Runtime.Store

end
