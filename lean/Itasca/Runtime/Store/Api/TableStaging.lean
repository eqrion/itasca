import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.TypeStaging

/-!
Table staging effects and their allocation loop. Imported binding and final preparation-result certificates remain separate to avoid a dependency cycle through PreparationResults.
-/

/-! ## Table Staging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def TableStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (ty : Itasca.wasm_types.TableType)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ tables elements addresses count,
    elements.val = List.replicate ty.limits.min.val 0#u64 ∧
    tables.val = store.tables.val ++ [{elements, ty := ty.elem, maximum := ty.limits.max}] ∧
    addresses.val = inst.tables.val ++ [{store := store.id, index := store.tables.len}] ∧
    LimitsFit ty.limits core.num.U32.MAX ∧ objectCount store < store.limits.max_objects.val ∧
    count.val = store.table_elements.val + ty.limits.min.val ∧ count.val ≤ store.limits.max_table_elements.val ∧
    out = (.Ok (), {store with tables, table_elements := count}, {inst with tables := addresses}))

theorem add_instance_table_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (bound : index.val < inst.module.module.env.table_types.val.length)
    (objectBound : objectCount store ≤ Usize.max) (room : inst.tables.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_table memory allocator store inst index
      ⦃ out => TableStageEffect store inst inst.module.module.env.table_types.val[index.val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_table
  simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, bind_ok]
  have sliceBound : index.val < inst.module.module.env.table_types.deref.length := by
    simpa [alloc.vec.Vec.deref] using bound
  step as ⟨ty, read⟩
  have same : ty = inst.module.module.env.table_types.val[index.val] := by simpa [alloc.vec.Vec.deref] using read
  clear read
  subst ty
  step with define_table_effect memory allocator law store _ objectBound as ⟨status, after, effect⟩
  rcases effect with ⟨error, failed⟩ | ⟨tables, elements, count, zeros, appended, limits, capacity, counter, budget, created⟩
  · rcases failed with ⟨rfl, rfl⟩
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, TableStageEffect]
  · rcases created with ⟨rfl, rfl⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨addresses, mapped⟩
    exact Or.inr ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩

theorem TableStageEffect.context {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    (bound : objectCount store ≤ Usize.max) :
    out.2.1 = {store with tables := out.2.1.tables, table_elements := out.2.1.table_elements} ∧
    out.2.2 = {inst with tables := out.2.2.tables} ∧ StagedPrefix store out.2.1 ∧ objectCount out.2.1 ≤ Usize.max := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact ⟨rfl, rfl, .refl _, bound⟩
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · constructor <;> simp [appended]
    · have maximum : store.limits.max_objects.val ≤ Usize.max := by scalar_tac
      have count : tables.length = store.tables.length + 1 := by simpa using congrArg List.length appended
      unfold objectCount at *
      dsimp only
      omega

theorem TableStageEffect.issued {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    (issued : ∀ address ∈ inst.tables.val, address.index.val < store.tables.length) :
    ∀ address ∈ out.2.2.tables.val, address.index.val < out.2.1.tables.length := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact issued
  · have count : tables.length = store.tables.length + 1 := by simpa using congrArg List.length appended
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · have bound := issued address old
      dsimp only
      omega
    · dsimp only
      simp [count]

theorem TableStageEffect.count {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    (success : out.1 = .Ok ()) : out.2.2.tables.length = inst.tables.length + 1 := by
  rcases effect with ⟨error, failed⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, output⟩
  · rw [failed] at success; cases success
  · rw [output]
    simpa using congrArg List.length mapped

end Itasca.Runtime.Store

end

/-! ## Table Staging Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual table allocation loop establishes complete issued table maps,
while retaining all old store objects and all other provisional maps. -/
theorem table_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
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
        (status = .Ok () → next.tables.length = seed.module.module.env.table_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.table_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop5
  apply loop.spec_decr_nat (fun state => seed.module.module.env.table_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with tables := state.1.tables, table_elements := state.1.table_elements} ∧
      state.2.2.2 = {seed with tables := state.2.2.2.tables} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.tables.val, address.index.val < state.1.tables.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.table_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.tables.length = state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop5.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.table_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp⟩
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
          effect.issued currentIssued, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.table_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, fun _ => count⟩

end Itasca.Runtime.Store

end
