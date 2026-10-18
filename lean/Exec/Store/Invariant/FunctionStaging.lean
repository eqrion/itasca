import Exec.Store.Invariant.TypeStaging

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The exact defined-function append, including its future instance identity
and canonical type index. No execution property of its body is assumed. -/
def FunctionStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.Instance)
    (instanceIndex index signature : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.Instance) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ functions addresses,
    functions.val = store.funcs.val ++ [{signature, code := .Wasm instanceIndex index}] ∧
    addresses.val = inst.funcs.val ++ [{store := store.id, index := store.funcs.len}] ∧
    objectCount store < store.limits.max_objects.val ∧
    out = (.Ok (), {store with funcs := functions}, {inst with funcs := addresses}))

theorem add_instance_function_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (instanceIndex index : Usize)
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
        runtime.compiler.ExecutableModule.env, module.Module.env,
        Itasca.module.Module.impl.env, module.Env.func_type_indices,
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
    {inst : runtime.store.Instance} {instanceIndex index signature out}
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
    {inst : runtime.store.Instance} {instanceIndex index signature out}
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
    {inst : runtime.store.Instance} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out) (success : out.1 = .Ok ()) :
    out.2.2.funcs.length = inst.funcs.length + 1 := by
  rcases effect with ⟨error, failed⟩ | ⟨functions, addresses, appended, mapped, capacity, output⟩
  · rw [failed] at success; cases success
  · rw [output]
    simpa using congrArg List.length mapped

end Exec.Store
