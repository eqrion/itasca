import Exec.Representation.Collection
import Exec.Store.Initialization.Initializer

namespace Exec.Store
open Aeneas Aeneas.Std

theorem StagedPrefix.set_fresh_instance {M : Type} {before after : runtime.store.Store M}
    (hprefix : StagedPrefix before after) (index : Usize) (inst : runtime.store.Instance)
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

theorem add_instance_global_staged {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (global : Itasca.module.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hprefix : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
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
      ⦃ out => StagedPrefix before out.2.1 ∧ out.2.2 = platform ⦄ := by
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hprefix
  | Ok value =>
    obtain ⟨owned, typed⟩ := hvalue value rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with define_global_effect memory allocator law store global.gtype value objectBound typed.symm owned
      as ⟨result, after, effect⟩
    rcases effect with ⟨error, failed⟩ | ⟨globals, words, encoded, hglobals, room, updated⟩
    · rcases failed with ⟨rfl, rfl⟩
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hprefix
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
      have appended : StagedPrefix store { store with globals := globals } := by
        constructor <;> simp [hglobals]
      have staged := (hprefix.trans appended).set_fresh_instance instIndex
        { inst with globals := addresses } fresh
      have instanceRead : store.instances.val[instIndex.val] = inst :=
        Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
      simpa [hback, instanceRead] using And.intro staged (rfl : platform = platform)

end Exec.Store
