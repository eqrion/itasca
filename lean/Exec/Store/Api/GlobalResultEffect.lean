import Exec.Representation.Collection
import Exec.Store.Api.GlobalEffects

/-! Exact append effects of staged globals, sufficient to propagate imported
constant contexts through the complete global initialization loop. -/
namespace Exec.Store
open Aeneas Aeneas.Std

inductive GlobalResultEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.Instance) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : GlobalResultEffect store instIndex inst (.Err error) store
  | appended (globals : alloc.vec.Vec runtime.store.GlobalInstance)
      (addresses : alloc.vec.Vec runtime.GlobalAddr) (global : runtime.store.GlobalInstance)
      (globalValues : globals.val = store.globals.val ++ [global])
      (addressValues : addresses.val = inst.globals.val ++ [⟨store.id, store.globals.len⟩])
      (canonical : GlobalShape store global)
      (room : objectCount store < store.limits.max_objects.val) :
      GlobalResultEffect store instIndex inst (.Ok ())
        { store with globals := globals, instances := store.instances.set instIndex { inst with globals := addresses } }

theorem add_instance_global_result_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (global : Itasca.module.Global)
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
      ⦃ out => GlobalResultEffect store instIndex inst out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
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
  step with eval_const_exec_owned memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved bindings
    as ⟨evaluated, store', platform', hs, hp, hvalue⟩
  subst store' platform'
  cases evaluated with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (GlobalResultEffect.failed (store := store) (instIndex := instIndex) (inst := inst) error)
  | Ok value =>
    obtain ⟨owned, typed⟩ := hvalue value rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with define_global_effect memory allocator law store global.gtype value objectBound typed.symm owned
      as ⟨result, after, effect⟩
    rcases effect with ⟨error, failed⟩ | ⟨globals, words, encoded, hglobals, room, updated⟩
    · rcases failed with ⟨rfl, rfl⟩
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using
          (GlobalResultEffect.failed (store := after) (instIndex := instIndex) (inst := inst) error)
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
      have effect := GlobalResultEffect.appended (store := store) (instIndex := instIndex) (inst := inst) globals addresses
        {ty := global.gtype, lo := words.1, hi := words.2} hglobals (by simpa only [instanceRead] using haddresses) canonical room
      simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

theorem GlobalResultEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst status} (effect : GlobalResultEffect store instIndex inst status after) :
    GlobalStageEffect store instIndex inst after := by
  cases effect with
  | failed error => exact .unchanged
  | appended globals addresses global stored mapped canonical room => exact .appended globals addresses global stored mapped canonical room

theorem GlobalResultEffect.count {M : Type} {store after : runtime.store.Store M}
    {instIndex inst status} (effect : GlobalResultEffect store instIndex inst status after)
    (bound : instIndex.val < store.instances.length) {next : runtime.store.Instance}
    (found : after.instances.val[instIndex.val]? = some next) (success : status = .Ok ()) :
    next.globals.length = inst.globals.length + 1 := by
  cases effect with
  | failed error => simp at success
  | appended globals addresses global stored mapped canonical room =>
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at found
    subst next
    simp [mapped]

def GlobalContents {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ global ∈ store.globals.val, GlobalShape store global

theorem GlobalStageEffect.contents {M : Type} {store after : runtime.store.Store M}
    {instIndex inst} (effect : GlobalStageEffect store instIndex inst after)
    (contents : GlobalContents store) : GlobalContents after := by
  cases effect with
  | unchanged => exact contents
  | appended globals addresses global stored mapped canonical room =>
    intro value member
    simp only [stored, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · simpa only [GlobalShape, ReferenceShape] using contents value old
    · simpa only [GlobalShape, ReferenceShape] using canonical

end Exec.Store
