import Exec.Store.Api.TableMemoryOrder
import Exec.Store.Invariant.TypeStagingLoop
import Exec.Store.Preparation.PreparationResults

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The actual table loop allocates a decoded source suffix in order and issues
consecutive fresh addresses, preserving all previous objects. -/
theorem table_allocation_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (count : inst.tables.length = start.val)
    (base : Nat) (initial : List Nat) (allocationStart : Nat) (original : List tableinst)
    (startOrder : allocationStart ≤ start.val)
    (ordered : AddressOrder base initial store.tables.length (inst.tables.val.map fun address => address.index.val))
    (matching : AllocationPrefix (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty))
      seed.module.module.env.table_types.val allocationStart original (store.tables.val.map decodeTable) start.val) :
    runtime.store.instantiate.Store.instantiate_inner_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        AddressOrder base initial after.tables.length (next.tables.val.map fun address => address.index.val) ∧
        (status = .Ok () → AllocationPrefix (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty))
          seed.module.module.env.table_types.val allocationStart original (after.tables.val.map decodeTable)
          seed.module.module.env.table_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.instantiate_inner_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      allocationStart ≤ state.2.2.1.val ∧
      AddressOrder base initial state.1.tables.length (state.2.2.2.tables.val.map fun address => address.index.val) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → AllocationPrefix (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty))
        seed.module.module.env.table_types.val allocationStart original (state.1.tables.val.map decodeTable) state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexLower, currentOrder, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexLower currentOrder indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.instantiate_inner_loop5.body
    simp only [runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
      module.Env.table_types, Itasca.module.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, currentOrder, by simp⟩
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
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
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


/-- An accepted full table allocation run has the exact source-defined append
and the consecutive address map required by module allocation. -/
theorem table_allocation_success {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before after : runtime.store.Store M) (inst next : runtime.store.ModuleInst) (start : Usize)
    (bound : start.val ≤ inst.module.module.env.table_types.val.length)
    (objectBound : objectCount before ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < before.tables.length)
    (count : inst.tables.length = start.val)
    (run : runtime.store.instantiate.Store.instantiate_inner_loop5 memory allocator before (.Ok ()) start inst =
      .ok (typeParts after (.Ok ()) next)) :
    after.tables.val.map decodeTable = before.tables.val.map decodeTable ++
      (inst.module.module.env.table_types.val.drop start.val).map
        (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty)) ∧
    after.tables.length = before.tables.length + (inst.module.module.env.table_types.val.length - start.val) ∧
    next.tables.val.map (fun address => address.index.val) =
      inst.tables.val.map (fun address => address.index.val) ++
        List.range' before.tables.length (inst.module.module.env.table_types.val.length - start.val) := by
  have checked := table_allocation_staging_loop memory allocator law before before inst inst start bound rfl rfl
    (.refl _) objectBound issued count before.tables.length (inst.tables.val.map fun address => address.index.val)
    start.val (before.tables.val.map decodeTable) (by omega) (.refl _ _) (.initial _ _ _ _)
  rw [run, WP.spec_ok] at checked
  obtain ⟨actual, actualInst, status, same, changed, instChanged, retained, objects, addresses, finalCount, ordered, contents⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := (typeParts_inj _ _ _ _ _ _).mp same
  have fullCount := finalCount rfl
  have complete := ordered.complete (count := inst.module.module.env.table_types.val.length - start.val)
    (by simp only [List.length_map]; change next.tables.length = inst.tables.length + _; omega)
  exact ⟨(contents rfl).complete, complete.1, complete.2⟩

end Exec.Store
