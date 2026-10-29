import Itasca.Runtime.Store.Api.TableStaging
import Itasca.Runtime.Store.Api.NewTableCauses
import Itasca.Runtime.Store.Preparation.PreparationCalls
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev tableStageCall {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (state : runtime.store.Store M × runtime.store.ModuleInst) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_table memory allocator state.1 state.2 index

def TableStagingCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (start : Usize) (limit : runtime.ResourceLimit) : Prop :=
  ∃ current currentInst index ty,
    PreparationCalls (tableStageCall memory allocator) (store,inst) start (current,currentInst) index ∧
    currentInst.module.module.env.table_types.val[index.val]? = some ty ∧
    runtime.store.instantiate.Store.add_instance_table memory allocator current currentInst index = .ok (.Err (.Exhausted limit),current,currentInst) ∧
    TableAllocationCause allocator current ty limit

/-- The actual table allocation loop establishes complete issued table maps,
while retaining all old store objects and all other provisional maps. -/
theorem table_staging_resource_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.table_types.val.length)
    (changed : store = {before with tables := store.tables, table_elements := store.table_elements})
    (instChanged : inst = {seed with tables := inst.tables})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length)
    (count : inst.tables.length = start.val)
    :
    runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with tables := after.tables, table_elements := after.table_elements} ∧ next = {seed with tables := next.tables} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.tables.val, address.index.val < after.tables.length) ∧
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ∧
        (∀ limit, status = .Err (.Exhausted limit) → TableStagingCause memory allocator store inst start limit) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → PreparationCalls (tableStageCall memory allocator) (store,inst) start (state.1,state.2.2.2) state.2.2.1) ∧
      (∀ limit, state.2.1 = .Err (.Exhausted limit) → TableStagingCause memory allocator store inst start limit))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, trace, cause⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
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
          mapChanged, prefixStore, bound, currentIssued, by simp, cause⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.table_types.val.length := by simpa only [source] using within
        have room : currentInst.tables.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have reached := trace rfl
        obtain ⟨⟨status,after,nextInst⟩,called,effect⟩ := WP.spec_imp_exists
          (add_instance_table_effect memory allocator law current currentInst index actualBound bound room)
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
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
          effect.issued currentIssued, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          subst status
          exact .next reached called increment
        · intro limit rejected
          subst status
          let ty := currentInst.module.module.env.table_types.val[index.val]
          have found : currentInst.module.module.env.table_types.val[index.val]? = some ty := List.getElem?_eq_getElem actualBound
          obtain ⟨unchanged,sameInst,refusal⟩ :=
            add_table_resource_cause memory allocator law current currentInst index ty found bound limit after nextInst called
          subst after
          subst nextInst
          exact ⟨current,currentInst,index,ty,reached,found,called,refusal⟩
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, cause⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => .refl _ _), by simp⟩

end Itasca.Runtime.Store
