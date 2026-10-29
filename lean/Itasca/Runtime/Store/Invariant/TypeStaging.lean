import Itasca.Runtime.Representation.TypeEntries
import Itasca.Runtime.Store.Preparation.Staging

/-!
Type interning and staging preserve context and type entries through the allocation loop. Resource classification remains a separate consumer shared with function staging.
-/

/-! ## Type Staging -/

section

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

end

/-! ## Type Staging Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def typeParts {M : Type} (store : runtime.store.Store M)
    (status : core.result.Result Unit runtime.ExecError) (inst : runtime.store.ModuleInst) :=
  (store, status, inst.module, inst.types, inst.funcs, inst.tables, inst.memories, inst.globals, inst.elems, inst.datas)

/-- Type canonicalization is total and preserves all other prepared maps. Its
successful type vector resolves every source signature to an exact store entry. -/
theorem type_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize) (startBound : start.val ≤ seed.module.module.env.types.val.length)
    (changed : store = {before with types := store.types, signature_values := store.signature_values})
    (instChanged : inst = {seed with types := inst.types})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (entries : TypeEntries store (seed.module.module.env.types.val.take start.val) inst.types.val) :
    runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with types := after.types, signature_values := after.signature_values} ∧
        next = {seed with types := next.types} ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧
        (status = .Ok () → TypeEntries after seed.module.module.env.types.val next.types.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop3
  apply loop.spec_decr_nat (fun state => seed.module.module.env.types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with types := state.1.types, signature_values := state.1.signature_values} ∧
      state.2.2.2 = {seed with types := state.2.2.2.types} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ state.2.2.1.val ≤ seed.module.module.env.types.val.length ∧
      (state.2.1 = .Ok () → TypeEntries state.1 (seed.module.module.env.types.val.take state.2.2.1.val)
        state.2.2.2.types.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, indexBound, typing⟩
    dsimp only at currentChanged mapChanged prefixStore bound indexBound typing ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop3.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, by simp⟩
      | Ok value =>
        cases value
        have typed := typing rfl
        have mapSize : currentInst.types.val.length = index.val := by
          have lengths := typed.length_eq
          simpa [List.length_take, Nat.min_eq_left indexBound] using lengths.symm
        have maximum := seed.module.module.env.types.property
        have room : currentInst.types.length < Usize.max := by change currentInst.types.val.length < Usize.max; omega
        have actualBound : index.val < currentInst.module.module.env.types.val.length := by simpa only [source] using within
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_type_effect memory allocator law current currentInst index actualBound bound room
          as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with types := after.types, signature_values := after.signature_values} := by
          calc
            after = {current with types := after.types, signature_values := after.signature_values} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with types := nextInst.types} := by
          calc
            nextInst = {currentInst with types := nextInst.types} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, ?_, ?_, ?_⟩
        · omega
        · intro success
          have extended := effect.entries success typed
          rw [increment, List.take_succ_eq_append_getElem within]
          simpa only [source] using extended
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, ?_⟩
      intro success
      simpa only [atEnd, List.take_length] using typing success
  · exact ⟨changed, instChanged, retained, objectBound, startBound, fun _ => entries⟩

end Itasca.Runtime.Store

end
