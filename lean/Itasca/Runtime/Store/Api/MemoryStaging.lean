import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Store.Invariant.TypeStaging

/-!
Memory staging effects and their allocation loop. Imported binding and final preparation-result certificates remain separate to avoid a dependency cycle through PreparationResults.
-/

/-! ## Memory Staging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def MemoryStageEffect {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (ty : Itasca.types.MemType)
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
  simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.mem_types, bind_ok]
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
    simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.mem_types, source, bind_ok]
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
