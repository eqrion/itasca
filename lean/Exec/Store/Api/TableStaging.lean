import Exec.Store.Preparation.Staging

namespace Exec.Store
open Aeneas Aeneas.Std

def TableStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.Instance)
    (ty : Itasca.types.TableType)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.Instance) : Prop :=
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
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (index : Usize)
    (bound : index.val < inst.module.module.env.table_types.val.length)
    (objectBound : objectCount store ≤ Usize.max) (room : inst.tables.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_table memory allocator store inst index
      ⦃ out => TableStageEffect store inst inst.module.module.env.table_types.val[index.val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_table
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
    module.Env.table_types, Itasca.module.Env.impl.table_types, bind_ok]
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
    {inst : runtime.store.Instance} {ty out} (effect : TableStageEffect store inst ty out)
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
    {inst : runtime.store.Instance} {ty out} (effect : TableStageEffect store inst ty out)
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
    {inst : runtime.store.Instance} {ty out} (effect : TableStageEffect store inst ty out)
    (success : out.1 = .Ok ()) : out.2.2.tables.length = inst.tables.length + 1 := by
  rcases effect with ⟨error, failed⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, output⟩
  · rw [failed] at success; cases success
  · rw [output]
    simpa using congrArg List.length mapped

end Exec.Store
