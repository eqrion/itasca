import Exec.Representation.Collection
import Exec.Store.Api.GlobalStaging
import Exec.Store.Initialization.InitializerCertificates

/-! Exact append effects of staged globals, sufficient to propagate imported
constant contexts through the complete global initialization loop. -/
namespace Exec.Store
open Aeneas Aeneas.Std

inductive GlobalStageEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) : runtime.store.Store M → Prop where
  | unchanged : GlobalStageEffect store instIndex inst store
  | appended (globals : alloc.vec.Vec runtime.store.GlobalInst)
      (addresses : alloc.vec.Vec runtime.GlobalAddr) (global : runtime.store.GlobalInst)
      (globalValues : globals.val = store.globals.val ++ [global])
      (addressValues : addresses.val = inst.globals.val ++ [⟨store.id, store.globals.len⟩])
      (canonical : GlobalShape store global)
      (room : objectCount store < store.limits.max_objects.val) :
      GlobalStageEffect store instIndex inst
        { store with globals := globals, instances := store.instances.set instIndex { inst with globals := addresses } }

theorem add_instance_global_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (global : Itasca.module.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (mapRoom : inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index
      ⦃ out => GlobalStageEffect store instIndex inst out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_global
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.globals, Itasca.module.Env.impl.globals, bind_ok]
  step with Exec.Representation.slice_index_given inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg) as ⟨found, hfound⟩
  subst found
  step with Interp.vec_index_given inst.module.global_initializers index function hmapping
    as ⟨found, hfound⟩
  subst found
  step with eval_const_owned memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved bindings
    as ⟨evaluated, store', platform', hs, hp, hvalue⟩
  subst store' platform'
  cases evaluated with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (GlobalStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
  | Ok value =>
    obtain ⟨owned, typed⟩ := hvalue value rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with define_global_effect memory allocator law store global.gtype value objectBound typed.symm owned
      as ⟨result, after, effect⟩
    rcases effect with ⟨error, failed⟩ | ⟨globals, words, encoded, hglobals, room, updated⟩
    · rcases failed with ⟨rfl, rfl⟩
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using
          (GlobalStageEffect.unchanged (store := after) (instIndex := instIndex) (inst := inst))
    · rcases updated with ⟨rfl, rfl⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have instanceBound : instIndex.val < store.instances.length :=
        (List.getElem?_eq_some_iff.mp hi).1
      step as ⟨old, back, hold, hback⟩
      have old_eq : old = inst := by
        have hread := List.getElem?_eq_getElem instanceBound
        rw [hi] at hread
        exact hold.trans (Option.some.inj hread).symm
      subst old
      step as ⟨addresses, haddresses⟩
      have canonical := encode_global_shape store value global.gtype typed.symm owned
      rw [encoded] at canonical
      simp only [WP.spec_ok] at canonical
      have instanceRead : store.instances.val[instIndex.val] = inst :=
        Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
      have effect := GlobalStageEffect.appended (store := store) (instIndex := instIndex) (inst := inst) globals addresses
        {ty := global.gtype, lo := words.1, hi := words.2} hglobals (by simpa only [instanceRead] using haddresses) canonical room
      simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

/-- The exact append effect preserves constant contexts and their source module,
and grows the instance global map by at most one address. -/
theorem GlobalStageEffect.context {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    ∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
      InitializerBindings after next ∧ InitializerImports after next ∧
      InitializerSegmentBindings after next ∧ next.globals.length ≤ inst.globals.length + 1 ∧
      next.elems = inst.elems ∧ next.datas = inst.datas := by
  cases effect with
  | unchanged => exact ⟨inst, found, rfl, bindings, imports, segments, by omega, rfl, rfl⟩
  | appended globals addresses global globalValues addressValues canonical room =>
    have bound : instIndex.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    refine ⟨{inst with globals := addresses}, ?_, rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp [alloc.vec.Vec.set_val_eq, List.getElem?_set, bound]
    · constructor
      · exact bindings.funcs
      · intro value member
        change value ∈ globals.val at member
        rw [globalValues] at member
        rcases List.mem_append.mp member with old | new
        · simpa only [GlobalShape, ReferenceShape] using bindings.globals value old
        · simp only [List.mem_singleton] at new
          subst value
          simpa only [GlobalShape, ReferenceShape] using canonical
    · exact imports.extend rfl rfl (by simp [addressValues]) (by simp [globalValues])
    · exact ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩
    · simp [addressValues]

theorem GlobalStageEffect.segments {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store instIndex inst after) :
    after.elems = store.elems ∧ after.datas = store.datas := by
  cases effect <;> exact ⟨rfl, rfl⟩

theorem GlobalStageEffect.object_bound {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store instIndex inst after)
    (bound : objectCount store ≤ Usize.max) : objectCount after ≤ Usize.max := by
  cases effect with
  | unchanged => exact bound
  | appended globals addresses global globalValues addressValues canonical room =>
    simp only [objectCount, alloc.vec.Vec.length, globalValues, List.length_append, List.length_singleton] at room ⊢
    scalar_tac

theorem GlobalStageEffect.staged {M : Type} {before store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store instIndex inst after)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val) :
    StagedPrefix before after := by
  cases effect with
  | unchanged => exact staged
  | appended globals addresses global globalValues addressValues canonical room =>
    have appended : StagedPrefix store {store with globals := globals} := by
      constructor <;> simp [globalValues]
    exact (staged.trans appended).set_fresh_instance instIndex {inst with globals := addresses} fresh

end Exec.Store
