import Itasca.Runtime.Representation.TypeEntries
import Itasca.Runtime.Store.Preparation.Staging

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A successful type-map entry names the exact canonical type; rejection
leaves both the store and provisional instance unchanged. -/
def TypeStageEffect {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (ty : Itasca.types.FuncType)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst) : Prop :=
  (∃ error, out = (.Err error, store, inst)) ∨
  (∃ index addresses,
    InternEffect store ty (.Ok index, out.2.1) ∧
    addresses.val = inst.types.val ++ [index] ∧
    out.1 = .Ok () ∧ out.2.2 = {inst with types := addresses})

theorem add_instance_type_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (bound : index.val < inst.module.module.env.types.val.length)
    (objectBound : objectCount store ≤ Usize.max) (room : inst.types.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_type memory allocator store inst index
      ⦃ out => TypeStageEffect store inst inst.module.module.env.types.val[index.val] out ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_type
  simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.types, bind_ok]
  have sliceBound : index.val < inst.module.module.env.types.deref.length := by
    simpa [alloc.vec.Vec.deref] using bound
  step as ⟨ty, read⟩
  have same : ty = inst.module.module.env.types.val[index.val] := by simpa [alloc.vec.Vec.deref] using read
  clear read
  subst ty
  step with intern_type_effect memory allocator law store _ objectBound as ⟨status, after, effect⟩
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, TypeStageEffect]
  · cases existing
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨addresses, mapped⟩
    exact Or.inr ⟨canonical, addresses, Or.inr (Or.inl ⟨canonical, found, rfl⟩), mapped, rfl, rfl⟩
  · cases created
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨addresses, mapped⟩
    exact Or.inr ⟨_, addresses, Or.inr (Or.inr ⟨types, count, appended, fresh, capacity, counter, limit, rfl⟩), mapped, rfl, rfl⟩

theorem InternEffect.lookup {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.types.FuncType} {index : Usize}
    (effect : InternEffect store ty (.Ok index, after)) : after.types.val[index.val]? = some ty := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed
  · cases existing; exact found
  · cases created; simp [appended]

theorem InternEffect.staged {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.types.FuncType} {status}
    (effect : InternEffect store ty (status, after)) : StagedPrefix store after := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed; exact .refl _
  · cases existing; exact .refl _
  · cases created; constructor <;> simp [appended]

theorem InternEffect.object_bound {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.types.FuncType} {status}
    (effect : InternEffect store ty (status, after)) (bound : objectCount store ≤ Usize.max) :
    objectCount after ≤ Usize.max := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ | ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed; exact bound
  · cases existing; exact bound
  · cases created
    have maximum : store.limits.max_objects.val ≤ Usize.max := by scalar_tac
    have length := congrArg List.length appended
    simp only [List.length_append, List.length_singleton] at length
    unfold objectCount at *
    change types.val.length = store.types.length + 1 at length
    dsimp only
    change types.length = store.types.length + 1 at length
    omega

theorem InternEffect.only_types {M : Type} {store after : runtime.store.Store M}
    {ty : Itasca.types.FuncType} {status} (effect : InternEffect store ty (status, after)) :
    after = {store with types := after.types, signature_values := after.signature_values} := by
  rcases effect with ⟨error, failed⟩ | ⟨canonical, found, existing⟩ |
    ⟨types, count, appended, fresh, capacity, counter, limit, created⟩
  · cases failed; rfl
  · cases existing; rfl
  · cases created; rfl

theorem TypeEntries.extend {M : Type} {store after : runtime.store.Store M}
    {source : List Itasca.types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) (retained : StagedPrefix store after) :
    TypeEntries after source indices := by
  apply List.Forall₂.imp ?_ entries
  intro ty index found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [← retained.types, List.getElem?_take] at found
  simpa [bound] using found

theorem TypeStageEffect.context {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty : Itasca.types.FuncType} {out}
    (effect : TypeStageEffect store inst ty out) (bound : objectCount store ≤ Usize.max) :
    out.2.1 = {store with types := out.2.1.types, signature_values := out.2.1.signature_values} ∧
    out.2.2 = {inst with types := out.2.2.types} ∧ StagedPrefix store out.2.1 ∧
    objectCount out.2.1 ≤ Usize.max := by
  rcases effect with ⟨error, rfl⟩ | ⟨index, addresses, interned, mapped, ok, next⟩
  · exact ⟨rfl, rfl, .refl _, bound⟩
  · exact ⟨interned.only_types, by rw [next], interned.staged, interned.object_bound bound⟩

theorem TypeStageEffect.entries {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty : Itasca.types.FuncType} {out}
    (effect : TypeStageEffect store inst ty out) (success : out.1 = .Ok ())
    {source : List Itasca.types.FuncType} (entries : TypeEntries store source inst.types.val) :
    TypeEntries out.2.1 (source ++ [ty]) out.2.2.types.val := by
  rcases effect with ⟨error, failed⟩ | ⟨index, addresses, interned, mapped, ok, next⟩
  · rw [failed] at success; cases success
  · rw [next]
    dsimp only
    rw [mapped]
    exact List.rel_append (entries.extend interned.staged) (.cons interned.lookup .nil)

end Itasca.Runtime.Store
