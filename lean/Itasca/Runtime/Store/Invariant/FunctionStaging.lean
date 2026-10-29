import Itasca.Runtime.Store.Invariant.TypeStaging

/-!
Function staging effect, issued-address retention and allocation-loop preservation. Resource causes remain separate because they also depend on type allocation.
-/

/-! ## Function Staging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The exact defined-function append, including its future instance identity
and canonical type index. No execution property of its body is assumed. -/
def FunctionStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (instanceIndex index signature : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ functions addresses,
    functions.val = store.funcs.val ++ [{signature, code := .Wasm instanceIndex index}] ∧
    addresses.val = inst.funcs.val ++ [{store := store.id, index := store.funcs.len}] ∧
    objectCount store < store.limits.max_objects.val ∧
    out = (.Ok (), {store with funcs := functions}, {inst with funcs := addresses}))

theorem add_instance_function_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (objectBound : objectCount store ≤ Usize.max)
    (bound : index.val < inst.module.module.env.func_type_indices.val.length)
    (typeBound : inst.module.module.env.func_type_indices.val[index.val].val < inst.types.val.length)
    (room : inst.funcs.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_function memory allocator store inst instanceIndex index
      ⦃ out => FunctionStageEffect store inst instanceIndex index
        inst.types.val[inst.module.module.env.func_type_indices.val[index.val].val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_function
  step with room_spec memory store objectBound as ⟨available, capacity⟩
  rw [capacity]
  split
  · rename_i space
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer, reserved⟩ := reserve_wrapper_eq allocator law store.funcs 1#usize
    rw [reserved]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, FunctionStageEffect]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env,
        Itasca.module.Module.impl.env,
        Itasca.module.Env.impl.func_type_indices]
      have sourceBound : index.val < inst.module.module.env.func_type_indices.deref.length := by
        simpa [alloc.vec.Vec.deref] using bound
      step as ⟨sourceType, sourceRead⟩
      step as ⟨typeIndex, typeCast⟩
      have validType : typeIndex.val < inst.types.length := by
        simpa [typeCast, sourceRead, alloc.vec.Vec.deref] using typeBound
      step as ⟨signature, typeRead⟩
      have storeRoom : store.funcs.length < Usize.max := by
        unfold objectCount at space
        scalar_tac
      step as ⟨functions, appended⟩
      step as ⟨addresses, mapped⟩
      right
      refine ⟨functions, addresses, ?_, mapped, space, rfl⟩
      simpa [typeRead, typeCast, sourceRead, alloc.vec.Vec.deref] using appended
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, FunctionStageEffect]

theorem FunctionStageEffect.context {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (bound : objectCount store ≤ Usize.max) :
    out.2.1 = {store with funcs := out.2.1.funcs} ∧
    out.2.2 = {inst with funcs := out.2.2.funcs} ∧ StagedPrefix store out.2.1 ∧
    objectCount out.2.1 ≤ Usize.max ∧ out.2.2.funcs.length ≤ inst.funcs.length + 1 := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, capacity, rfl⟩
  · exact ⟨rfl, rfl, .refl _, bound, by simp⟩
  · refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · constructor <;> simp [appended]
    · have maximum : store.limits.max_objects.val ≤ Usize.max := by scalar_tac
      have count : functions.length = store.funcs.length + 1 := by simpa using congrArg List.length appended
      unfold objectCount at *
      dsimp only
      omega
    · exact le_of_eq (by simpa using congrArg List.length mapped)

theorem FunctionStageEffect.issued {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length) :
    ∀ address ∈ out.2.2.funcs.val, address.index.val < out.2.1.funcs.length := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, capacity, rfl⟩
  · exact issued
  · have count : functions.length = store.funcs.length + 1 := by simpa using congrArg List.length appended
    intro address member
    simp only [mapped, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · have bound := issued address old
      dsimp only
      omega
    · dsimp only
      simpa [count]

theorem FunctionStageEffect.count {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out) (success : out.1 = .Ok ()) :
    out.2.2.funcs.length = inst.funcs.length + 1 := by
  rcases effect with ⟨error, failed⟩ | ⟨functions, addresses, appended, mapped, capacity, output⟩
  · rw [failed] at success; cases success
  · rw [output]
    simpa using congrArg List.length mapped

end Itasca.Runtime.Store

end

/-! ## Function Staging Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
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
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
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
