import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Invariant.TypeStaging

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Type canonicalization is total and preserves all other prepared maps. Its
successful type vector resolves every source signature to an exact store entry. -/
theorem type_allocated_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize) (startBound : start.val ≤ seed.module.module.env.types.val.length)
    (changed : store = {before with types := store.types, signature_values := store.signature_values})
    (instChanged : inst = {seed with types := inst.types})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (entries : TypeEntries store (seed.module.module.env.types.val.take start.val) inst.types.val) :
    runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with types := after.types, signature_values := after.signature_values} ∧
        next = {seed with types := next.types} ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ AllocationShape view after ∧
        (status = .Ok () → TypeEntries after seed.module.module.env.types.val next.types.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop3
  apply loop.spec_decr_nat (fun state => seed.module.module.env.types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with types := state.1.types, signature_values := state.1.signature_values} ∧
      state.2.2.2 = {seed with types := state.2.2.2.types} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧ state.2.2.1.val ≤ seed.module.module.env.types.val.length ∧
      (state.2.1 = .Ok () → TypeEntries state.1 (seed.module.module.env.types.val.take state.2.2.1.val)
        state.2.2.2.types.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentAllocated, indexBound, typing⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentAllocated indexBound typing ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop3.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, currentAllocated, by simp⟩
      | Ok value =>
        cases value
        have typed := typing rfl
        have mapSize : currentInst.types.val.length = index.val := by
          have lengths := typed.length_eq
          simpa [List.length_take, Nat.min_eq_left indexBound] using lengths.symm
        have maximum := seed.module.module.env.types.property
        have room : currentInst.types.length < Usize.max := by change currentInst.types.val.length < Usize.max; omega
        have actualBound : index.val < currentInst.module.module.env.types.val.length := by simpa only [source] using within
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_type_effect memory allocator law current currentInst index actualBound bound room
          as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with types := after.types, signature_values := after.signature_values} := by
          calc
            after = {current with types := after.types, signature_values := after.signature_values} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with types := nextInst.types} := by
          calc
            nextInst = {currentInst with types := nextInst.types} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, effect.allocated currentAllocated, ?_, ?_, ?_⟩
        · omega
        · intro success
          have extended := effect.entries success typed
          rw [increment, List.take_succ_eq_append_getElem within]
          simpa only [source] using extended
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, currentAllocated, ?_⟩
      intro success
      simpa only [atEnd, List.take_length] using typing success
  · exact ⟨changed, instChanged, retained, objectBound, allocated, startBound, fun _ => entries⟩

end Itasca.Runtime.Store
