import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Module.Env.Basic
import Itasca.Module.Elab.TypingInversion
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Initialization.ElementLoop

/-!
Sections, each formerly its own module: MemoryStaging, TableStaging, TableMemoryBindings, ExportBounds, GlobalStaging, MemoryBindingLoop.
-/

/-! ## MemoryStaging -/

section

/-!
Memory staging effects and their allocation loop. Imported binding and final preparation-result certificates remain separate to avoid a dependency cycle through PreparationResults.
-/

/-! ## Memory Staging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryStageEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (ty : Itasca.wasm_types.MemType)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ memories buffer addresses count,
    (view buffer).val = List.replicate (ty.limits.min.val * 65536) 0#u8 ∧
    memories.val = store.memories.val ++ [{buf := buffer, maximum := ty.limits.max}] ∧
    addresses.val = inst.memories.val ++ [{store := store.id, index := store.memories.len}] ∧
    LimitsFit ty.limits 65536#u32 ∧ objectCount store < store.limits.max_objects.val ∧
    count.val = store.memory_bytes.val + (view buffer).length ∧ count.val ≤ store.limits.max_memory_bytes.val ∧
    out = (.Ok (), {store with memories, memory_bytes := count}, {inst with memories := addresses}))

theorem add_instance_memory_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (bound : index.val < inst.module.module.env.mem_types.val.length)
    (objectBound : objectCount store ≤ Usize.max) (room : inst.memories.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_memory memory allocator store inst index
      ⦃ out => MemoryStageEffect view store inst inst.module.module.env.mem_types.val[index.val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_memory
  simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, bind_ok]
  have sliceBound : index.val < inst.module.module.env.mem_types.deref.length := by
    simpa [alloc.vec.Vec.deref] using bound
  step as ⟨ty, read⟩
  have same : ty = inst.module.module.env.mem_types.val[index.val] := by simpa [alloc.vec.Vec.deref] using read
  clear read
  subst ty
  step as ⟨minimum, hminimum⟩
  step as ⟨bytes, hbytes⟩
  step as ⟨maximum, hmaximum⟩
  split
  · simp [MemoryStageEffect]
  · rename_i fits
    step as ⟨size, hsize⟩
    step with within_spec store.memory_bytes size store.limits.max_memory_bytes as ⟨within, hwithin⟩
    cases within
    · simp [MemoryStageEffect]
    · simp
      step as ⟨size', hsize'⟩
      step with laws.create size' as ⟨buffer, hbuffer⟩
      cases buffer with
      | none => simp [MemoryStageEffect]
      | some buffer =>
        simp only
        have zeros : (view buffer).val = List.replicate
            (inst.module.module.env.mem_types.val[index.val].limits.min.val * 65536) 0#u8 := by
          have hz := hbuffer buffer rfl
          have exactSize : size'.val = inst.module.module.env.mem_types.val[index.val].limits.min.val * 65536 := by
            rcases Usize.bounds_eq with h | h <;> scalar_tac
          simpa only [exactSize] using hz
        step with define_memory_effect memory allocator law view laws store _ buffer objectBound
          as ⟨status, after, effect⟩
        rcases effect with ⟨error, failed⟩ | ⟨memories, count, appended, limits, sizeEq, capacity, counter, budget, created⟩
        · rcases failed with ⟨rfl, rfl⟩
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MemoryStageEffect]
        · rcases created with ⟨rfl, rfl⟩
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step as ⟨addresses, mapped⟩
          exact Or.inr ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩

theorem MemoryStageEffect.context {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : MemoryStageEffect view store inst ty out)
    (bound : objectCount store ≤ Usize.max) :
    out.2.1 = {store with memories := out.2.1.memories, memory_bytes := out.2.1.memory_bytes} ∧
    out.2.2 = {inst with memories := out.2.2.memories} ∧ StagedPrefix store out.2.1 ∧ objectCount out.2.1 ≤ Usize.max := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact ⟨rfl, rfl, .refl _, bound⟩
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · constructor <;> simp [appended]
    · have maximum : store.limits.max_objects.val ≤ Usize.max := by scalar_tac
      have count : memories.length = store.memories.length + 1 := by simpa using congrArg List.length appended
      unfold objectCount at *
      dsimp only
      omega

theorem MemoryStageEffect.issued {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : MemoryStageEffect view store inst ty out)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length) :
    ∀ address ∈ out.2.2.memories.val, address.index.val < out.2.1.memories.length := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · exact issued
  · have count : memories.length = store.memories.length + 1 := by simpa using congrArg List.length appended
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · have bound := issued address old
      dsimp only
      omega
    · dsimp only
      simp [count]

theorem MemoryStageEffect.count {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : MemoryStageEffect view store inst ty out)
    (success : out.1 = .Ok ()) : out.2.2.memories.length = inst.memories.length + 1 := by
  rcases effect with ⟨error, failed⟩ | ⟨memories, buffer, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, output⟩
  · rw [failed] at success; cases success
  · rw [output]
    simpa using congrArg List.length mapped

end Itasca.Runtime.Store

end

/-! ## Memory Staging Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual memory allocation loop establishes complete issued memory maps,
while retaining all old store objects and all other provisional maps. -/
theorem memory_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    :
    runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with memories := after.memories, memory_bytes := after.memory_bytes} ∧ next = {seed with memories := next.memories} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.memories.val, address.index.val < after.memories.length) ∧
        (status = .Ok () → next.memories.length = seed.module.module.env.mem_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.mem_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop6
  apply loop.spec_decr_nat (fun state => seed.module.module.env.mem_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with memories := state.1.memories, memory_bytes := state.1.memory_bytes} ∧
      state.2.2.2 = {seed with memories := state.2.2.2.memories} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.memories.val, address.index.val < state.1.memories.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.mem_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.memories.length = state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop6.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.mem_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp⟩
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
          effect.issued currentIssued, ?_, ?_, ?_⟩
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
        mapChanged, prefixStore, bound, currentIssued, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, fun _ => count⟩

end Itasca.Runtime.Store

end

end

/-! ## TableStaging -/

section

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

end

/-! ## TableMemoryBindings -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev TableBindings {M : Type} (store : runtime.store.Store M)
    (types : List Itasca.wasm_types.TableType) (addresses : List runtime.TableAddr) : Prop :=
  List.Forall₂ (ImportedTable store) types addresses

abbrev MemoryBindings {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (types : List Itasca.wasm_types.MemType) (addresses : List runtime.MemoryAddr) : Prop :=
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
    {types : List Itasca.wasm_types.TableType} (matching : TableBindings store types inst.tables.val)
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
    {types : List Itasca.wasm_types.MemType} (matching : MemoryBindings view store types inst.memories.val)
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

end

/-! ## ExportBounds -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Static export descriptors address the validated namespace and retain
unique source names. Both facts depend only on immutable module metadata. -/
structure ModuleExportBounds (env : Itasca.metadata.Env) : Prop where
  indices : ∀ entry ∈ env.exports.val, match entry.desc with
    | .Func index => index.val < env.func_types.length
    | .Table index => index.val < env.table_types.length
    | .Memory index => index.val < env.mem_types.length
    | .Global index => index.val < env.global_types.length
  names : (env.exports.val.map (fun entry => Itasca.ModuleBinary.nameOfBytes entry.name.val)).Nodup

/-- Every retained instance has bounded module export descriptors. -/
def ExportBounds {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ (index : Nat) (inst : runtime.store.ModuleInst), store.instances.val[index]? = some inst → ModuleExportBounds inst.module.module.env

/-- Successful validation supplies export bounds without an API correctness premise. -/
theorem module_export_bounds {env } (valid : Itasca.ModuleEnv.Valid env) :
    ModuleExportBounds env := by
  constructor
  · intro entry member
    obtain ⟨ty,resolved⟩ := valid.exports entry member
    cases descriptor : entry.desc <;>
      simp only [Itasca.ModuleExternals.ExportResolves,descriptor] at resolved ⊢ <;>
      exact resolved.choose
  · exact Itasca.ModuleElaboration.export_names_distinct valid

/-- Combining retained export descriptors with completed instance map lengths
makes every actual export address lookup safe. -/
theorem export_address_bounds {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (bounds : ModuleExportBounds inst.module.module.env)
    (shape : InstanceShape store inst) (entry : Itasca.metadata.Export)
    (member : entry ∈ inst.module.module.env.exports.val) :
    match entry.desc with
    | .Func index => index.val < inst.funcs.length
    | .Table index => index.val < inst.tables.length
    | .Memory index => index.val < inst.memories.length
    | .Global index => index.val < inst.globals.length := by
  obtain ⟨_,functions,tables,memories,globals,_⟩ := shape
  have bounded := bounds.indices entry member
  cases descriptor : entry.desc <;> simp only [descriptor] at bounded ⊢
  · simpa only [functions] using bounded
  · simpa only [tables] using bounded
  · simpa only [memories] using bounded
  · simpa only [globals] using bounded

theorem ExportBounds.instances_eq {M : Type} {before after : runtime.store.Store M}
    (bounds : ExportBounds before) (same : after.instances = before.instances) : ExportBounds after := by
  simpa only [ExportBounds,same] using bounds

theorem ExportBounds.staged {M : Type} {before after : runtime.store.Store M}
    (bounds : ExportBounds before) (retained : StagedPrefix before after)
    (count : after.instances.length ≤ before.instances.length + 1)
    (fresh : ∀ inst, after.instances.val[before.instances.length]? = some inst →
      ModuleExportBounds inst.module.module.env) : ExportBounds after := by
  intro index inst found
  by_cases bound : index < before.instances.length
  · have same := congrArg (fun values : List runtime.store.ModuleInst => values[index]?) retained.instances
    have oldFound : before.instances.val[index]? = some inst := by
      simpa only [List.getElem?_take, if_pos bound, found] using same.symm
    exact bounds index inst oldFound
  · have room := (List.getElem?_eq_some_iff.mp found).1
    change index < after.instances.length at room
    have equal : index = before.instances.length := by omega
    subst index
    exact fresh inst found

end Itasca.Runtime.Store

end

/-! ## GlobalStaging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem StagedPrefix.set_fresh_instance {M : Type} {before after : runtime.store.Store M}
    (hprefix : StagedPrefix before after) (index : Usize) (inst : runtime.store.ModuleInst)
    (fresh : before.instances.length ≤ index.val) :
    StagedPrefix before { after with instances := after.instances.set index inst } := by
  constructor
  · exact hprefix.identity
  · exact hprefix.limits
  · exact hprefix.funcs
  · exact hprefix.types
  · exact hprefix.tables
  · exact hprefix.memories
  · exact hprefix.globals
  · simpa [alloc.vec.Vec.set_val_eq, List.take_set_of_le fresh] using hprefix.instances
  · exact hprefix.elems
  · exact hprefix.datas
  · exact hprefix.externs
  · exact hprefix.instanceItems

end Itasca.Runtime.Store

end

/-! ## MemoryBindingLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual memory allocation loop retains import-compatible memory limits,
while retaining all old store objects and all other provisional maps. -/
theorem memory_binding_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (matching : MemoryBindings view store (seed.module.module.env.mem_types.val.take start.val) inst.memories.val) :
    runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with memories := after.memories, memory_bytes := after.memory_bytes} ∧ next = {seed with memories := next.memories} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.memories.val, address.index.val < after.memories.length) ∧
        (status = .Ok () → next.memories.length = seed.module.module.env.mem_types.val.length) ∧
        (status = .Ok () → MemoryBindings view after seed.module.module.env.mem_types.val next.memories.val) ⦄ := by
  have capacity := seed.module.module.env.mem_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop6
  apply loop.spec_decr_nat (fun state => seed.module.module.env.mem_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with memories := state.1.memories, memory_bytes := state.1.memory_bytes} ∧
      state.2.2.2 = {seed with memories := state.2.2.2.memories} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.memories.val, address.index.val < state.1.memories.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.mem_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.memories.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → MemoryBindings view state.1 (seed.module.module.env.mem_types.val.take state.2.2.1.val) state.2.2.2.memories.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop6.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.mem_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, by simp⟩
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
          effect.issued currentIssued, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have nextTyped := effect.memory_bindings (typed rfl) success
          simpa only [source, increment, List.take_succ_eq_append_getElem within] using nextTyped
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.mem_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd, List.take_length] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, (fun _ => count), (fun _ => matching)⟩

end Itasca.Runtime.Store

end
