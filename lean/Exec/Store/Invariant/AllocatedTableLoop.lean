import Exec.Store.Preparation.AllocationStorage
import Exec.Store.Api.TableTypes
import Exec.Store.Invariant.TypeStagingLoop

import Exec.Store.Preparation.StagingAddresses

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table allocation loop establishes complete issued table maps,
while retaining all old store objects and all other provisional maps. -/
theorem table_allocated_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (owners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (count : inst.tables.length = start.val)
    (matching : TableTypeMap store (seed.module.module.env.table_types.val.take start.val) inst.tables.val) :
    runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (∀ address ∈ next.tables.val, address.store = after.id) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        (status = .Ok () → TableTypeMap after seed.module.module.env.table_types.val next.tables.val) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      (∀ address ∈ state.2.2.2.tables.val, address.store = state.1.id) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → TableTypeMap state.1 (seed.module.module.env.table_types.val.take state.2.2.1.val) state.2.2.2.tables.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentAllocated currentIssued currentOwners indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop5.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, by simp, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.table_types.val.length := by simpa only [source] using within
        have room : currentInst.tables.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_table_effect memory allocator law current currentInst index
          actualBound bound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with tables := after.tables, table_elements := after.table_elements} := by
          calc
            after = {current with tables := after.tables, table_elements := after.table_elements} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with tables := nextInst.tables} := by
          calc
            nextInst = {currentInst with tables := nextInst.tables} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.allocated currentAllocated,
          effect.issued currentIssued, effect.owners currentOwners, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have nextTyped := effect.table_types (typed rfl) success
          simpa only [source, increment, List.take_succ_eq_append_getElem within] using nextTyped
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentAllocated, currentIssued, currentOwners, ?_, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd, List.take_length] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, allocated, issued, owners, startBound, (fun _ => count), (fun _ => matching)⟩

end Itasca.Runtime.Store
