import Itasca.Runtime.Store.Api.TableMemoryOrder
import Itasca.Runtime.Store.Invariant.TypeStaging
import Itasca.Runtime.Store.Preparation.PreparationResults

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual memory loop allocates a decoded source suffix in order and issues
consecutive fresh addresses, preserving all previous objects. -/
theorem memory_allocation_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.mem_types.val.length)
    (changed : store = {before with memories := store.memories, memory_bytes := store.memory_bytes})
    (instChanged : inst = {seed with memories := inst.memories})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length)
    (count : inst.memories.length = start.val)
    (base : Nat) (initial : List Nat) (allocationStart : Nat) (original : List meminst)
    (startOrder : allocationStart ≤ start.val)
    (ordered : AddressOrder base initial store.memories.length (inst.memories.val.map fun address => address.index.val))
    (matching : AllocationPrefix (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty))
      seed.module.module.env.mem_types.val allocationStart original (store.memories.val.map (decodeMemory view)) start.val) :
    runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with memories := after.memories, memory_bytes := after.memory_bytes} ∧ next = {seed with memories := next.memories} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.memories.val, address.index.val < after.memories.length) ∧
        (status = .Ok () → next.memories.length = seed.module.module.env.mem_types.val.length) ∧
        AddressOrder base initial after.memories.length (next.memories.val.map fun address => address.index.val) ∧
        (status = .Ok () → AllocationPrefix (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty))
          seed.module.module.env.mem_types.val allocationStart original (after.memories.val.map (decodeMemory view))
          seed.module.module.env.mem_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.mem_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop6
  apply loop.spec_decr_nat (fun state => seed.module.module.env.mem_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with memories := state.1.memories, memory_bytes := state.1.memory_bytes} ∧
      state.2.2.2 = {seed with memories := state.2.2.2.memories} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.memories.val, address.index.val < state.1.memories.length) ∧
      allocationStart ≤ state.2.2.1.val ∧
      AddressOrder base initial state.1.memories.length (state.2.2.2.memories.val.map fun address => address.index.val) ∧
      state.2.2.1.val ≤ seed.module.module.env.mem_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.memories.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → AllocationPrefix (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty))
        seed.module.module.env.mem_types.val allocationStart original (state.1.memories.val.map (decodeMemory view)) state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexLower, currentOrder, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexLower currentOrder indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop6.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.mem_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.mem_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, currentOrder, by simp⟩
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
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, effect.address_order currentOrder, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have grown := (typed rfl).append indexLower within
          have actual := effect.decoded success
          dsimp only at actual
          unfold AllocationPrefix
          rw [actual]
          simpa only [AllocationPrefix, source, increment] using grown
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.mem_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, currentOrder, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startOrder, ordered, startBound, (fun _ => count), (fun _ => matching)⟩


/-- An accepted full memory allocation run has the exact source-defined append
and the consecutive address map required by module allocation. -/
theorem memory_allocation_success {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before after : runtime.store.Store M) (inst next : runtime.store.ModuleInst) (start : Usize)
    (bound : start.val ≤ inst.module.module.env.mem_types.val.length)
    (objectBound : objectCount before ≤ Usize.max)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < before.memories.length)
    (count : inst.memories.length = start.val)
    (run : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator before (.Ok ()) start inst =
      .ok (typeParts after (.Ok ()) next)) :
    after.memories.val.map (decodeMemory view) = before.memories.val.map (decodeMemory view) ++
      (inst.module.module.env.mem_types.val.drop start.val).map
        (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty)) ∧
    after.memories.length = before.memories.length + (inst.module.module.env.mem_types.val.length - start.val) ∧
    next.memories.val.map (fun address => address.index.val) =
      inst.memories.val.map (fun address => address.index.val) ++
        List.range' before.memories.length (inst.module.module.env.mem_types.val.length - start.val) := by
  have checked := memory_allocation_staging_loop memory allocator law view laws before before inst inst start bound rfl rfl
    (.refl _) objectBound issued count before.memories.length (inst.memories.val.map fun address => address.index.val)
    start.val (before.memories.val.map (decodeMemory view)) (by omega) (.refl _ _) (.initial _ _ _ _)
  rw [run, WP.spec_ok] at checked
  obtain ⟨actual, actualInst, status, same, changed, instChanged, retained, objects, addresses, finalCount, ordered, contents⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := (type_parts_inj _ _ _ _ _ _).mp same
  have fullCount := finalCount rfl
  have complete := ordered.complete (count := inst.module.module.env.mem_types.val.length - start.val)
    (by simp only [List.length_map]; change next.memories.length = inst.memories.length + _; omega)
  exact ⟨(contents rfl).complete, complete.1, complete.2⟩

end Itasca.Runtime.Store
