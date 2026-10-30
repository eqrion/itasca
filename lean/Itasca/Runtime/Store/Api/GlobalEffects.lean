import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Api.GlobalStaging
import Itasca.Runtime.Store.Initialization.InitializerCertificates
import Itasca.Runtime.Store.Linking.LinkMaps
import Itasca.Runtime.Store.Invariant.ValueDecode
import Itasca.Runtime.Store.Initialization.InitializerSourceContext

/-!
Global allocation result, typed values and decoded source effect. These retain success and error distinctions used by preparation and instantiation.
-/

/-! ## Global Effects -/

section

/-! Exact append effects of staged globals, sufficient to propagate imported
constant contexts through the complete global initialization loop. -/
namespace Itasca.Runtime.Store
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
    (inst : runtime.store.ModuleInst) (global : Itasca.metadata.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (mapRoom : inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index
      ⦃ out => GlobalStageEffect store instIndex inst out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_global
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg) as ⟨found, hfound⟩
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

end Itasca.Runtime.Store

end

/-! ## Global Result Effect -/

section

/-! Exact append effects of staged globals, sufficient to propagate imported
constant contexts through the complete global initialization loop. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

inductive GlobalResultEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : GlobalResultEffect store instIndex inst (.Err error) store
  | appended (globals : alloc.vec.Vec runtime.store.GlobalInst)
      (addresses : alloc.vec.Vec runtime.GlobalAddr) (global : runtime.store.GlobalInst)
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
    (inst : runtime.store.ModuleInst) (global : Itasca.metadata.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (mapRoom : inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index
      ⦃ out => GlobalResultEffect store instIndex inst out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_global
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg) as ⟨found, hfound⟩
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
    (bound : instIndex.val < store.instances.length) {next : runtime.store.ModuleInst}
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

end Itasca.Runtime.Store

end

/-! ## Global Typed Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The appended global retains the exact validated source type. -/
inductive GlobalTypedEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) (ty : Itasca.wasm_types.GlobalType) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : GlobalTypedEffect store instIndex inst ty (.Err error) store
  | appended (globals : alloc.vec.Vec runtime.store.GlobalInst)
      (addresses : alloc.vec.Vec runtime.GlobalAddr) (lo hi : U64)
      (globalValues : globals.val = store.globals.val ++ [{ty := ty, lo := lo, hi := hi}])
      (addressValues : addresses.val = inst.globals.val ++ [⟨store.id, store.globals.len⟩])
      (canonical : GlobalShape store {ty := ty, lo := lo, hi := hi})
      (room : objectCount store < store.limits.max_objects.val) :
      GlobalTypedEffect store instIndex inst ty (.Ok ())
        {store with globals := globals, instances := store.instances.set instIndex {inst with globals := addresses}}

theorem GlobalTypedEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst ty status} (typed : GlobalTypedEffect store instIndex inst ty status after) :
    GlobalStageEffect store instIndex inst after := by
  cases typed with
  | failed error => exact .unchanged
  | appended globals addresses lo hi stored mapped canonical room =>
    exact .appended globals addresses _ stored mapped canonical room

theorem add_instance_global_typed_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (global : Itasca.metadata.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (mapRoom : inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index
      ⦃ out => GlobalTypedEffect store instIndex inst global.gtype out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_global
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg) as ⟨found, hfound⟩
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (GlobalTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (ty := global.gtype) error)
  | Ok value =>
    obtain ⟨owned, typed⟩ := hvalue value rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with define_global_effect memory allocator law store global.gtype value objectBound typed.symm owned
      as ⟨result, after, effect⟩
    rcases effect with ⟨error, failed⟩ | ⟨globals, words, encoded, hglobals, room, updated⟩
    · rcases failed with ⟨rfl, rfl⟩
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using
          (GlobalTypedEffect.failed (store := after) (instIndex := instIndex) (inst := inst) (ty := global.gtype) error)
    · rcases updated with ⟨rfl, rfl⟩
      simp only [bind_ok]
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
      have effect := GlobalTypedEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (ty := global.gtype) globals addresses words.1 words.2 hglobals (by simpa only [instanceRead] using haddresses) canonical room
      simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)


end Itasca.Runtime.Store

end

/-! ## Global Value Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The appended global retains its validated type and exact decoded initializer value. -/
inductive GlobalValueEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) (ty : Itasca.wasm_types.GlobalType) (value : val) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : GlobalValueEffect store instIndex inst ty value (.Err error) store
  | appended (globals : alloc.vec.Vec runtime.store.GlobalInst)
      (addresses : alloc.vec.Vec runtime.GlobalAddr) (lo hi : U64)
      (globalValues : globals.val = store.globals.val ++ [{ty := ty, lo := lo, hi := hi}])
      (addressValues : addresses.val = inst.globals.val ++ [⟨store.id, store.globals.len⟩])
      (canonical : GlobalShape store {ty := ty, lo := lo, hi := hi})
      (room : objectCount store < store.limits.max_objects.val)
      (decoded : decodeWords ty.valtype lo hi = value) :
      GlobalValueEffect store instIndex inst ty value (.Ok ())
        {store with globals := globals, instances := store.instances.set instIndex {inst with globals := addresses}}

theorem GlobalValueEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst ty value status} (typed : GlobalValueEffect store instIndex inst ty value status after) :
    GlobalStageEffect store instIndex inst after := by
  cases typed with
  | failed error => exact .unchanged
  | appended globals addresses lo hi stored mapped canonical room decoded =>
    exact .appended globals addresses _ stored mapped canonical room

theorem add_instance_global_value_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (global : Itasca.metadata.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (mapRoom : inst.globals.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index
      ⦃ out => GlobalValueEffect store instIndex inst global.gtype
        (decodeWords global.gtype.valtype ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)) out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  have exactValue := eval_const_effect memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved (initializer_reference_bound resolved bindings)
  obtain ⟨constantResult, constantRun, constantOwned⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code global.init global.gtype.valtype words hi hc compiled resolved bindings)
  rw [constantRun] at exactValue
  simp only [WP.spec_ok] at exactValue
  unfold runtime.store.instantiate.Store.add_instance_global
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg) as ⟨found, hfound⟩
  subst found
  step with Interp.vec_index_given inst.module.global_initializers index function hmapping
    as ⟨found, hfound⟩
  subst found
  rw [constantRun]
  simp only [bind_ok]
  rcases constantResult with ⟨evaluated, store', platform'⟩
  obtain ⟨hs, hp, hvalue⟩ := constantOwned
  dsimp only at hs hp exactValue hvalue ⊢
  subst store' platform'
  cases evaluated with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (GlobalValueEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (ty := global.gtype) error)
  | Ok value =>
    obtain ⟨owned, typed⟩ := hvalue value rfl
    have decodedValue := (exactValue.2.2 value rfl).2
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with define_global_effect memory allocator law store global.gtype value objectBound typed.symm owned
      as ⟨result, after, effect⟩
    rcases effect with ⟨error, failed⟩ | ⟨globals, words, encoded, hglobals, room, updated⟩
    · rcases failed with ⟨rfl, rfl⟩
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using
          (GlobalValueEffect.failed (store := after) (instIndex := instIndex) (inst := inst) (ty := global.gtype) error)
    · rcases updated with ⟨rfl, rfl⟩
      simp only [bind_ok]
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
      have effect := GlobalValueEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (ty := global.gtype) (value := Interp.sourceValue value) globals addresses words.1 words.2 hglobals (by simpa only [instanceRead] using haddresses) canonical room
        (by rw [← typed]; exact decode_encoded_value store value owned words encoded)
      simpa [hback, instanceRead, decodedValue] using And.intro effect (rfl : platform = platform)


end Itasca.Runtime.Store

end

/-! ## Global Value Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- Every appended runtime global has its declared type and its source
initializer's value in the unchanged initial source state. -/
def GlobalSourceValues (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (source : List Itasca.metadata.Global) (values : List runtime.store.GlobalInst) : Prop :=
  List.Forall₂ (fun original actual => actual.ty = original.gtype ∧
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (ModuleConstants.expression original.init)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [(decodeGlobal actual).VALUE]) source values

theorem GlobalStageEffect.source_context {M : Type} {store after : runtime.store.Store M}
    {instIndex inst next sourceStore sourceInstance}
    (effect : GlobalStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (imports : InitializerImports store inst)
    (context : InitializerSourceContext sourceStore sourceInstance store inst) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact context
  | appended globals addresses global stored mapped canonical room =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact context.extend imports rfl rfl (by simp [mapped]) (by simp [stored])

theorem GlobalValueEffect.source_values {M : Type} {store after : runtime.store.Store M}
    {instIndex inst sourceStore sourceInstance status value}
    {original : Itasca.metadata.Global}
    (effect : GlobalValueEffect store instIndex inst original.gtype value status after)
    (evaluated : Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      (ModuleConstants.expression original.init) ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [value])
    {sources : List Itasca.metadata.Global} {base produced : List runtime.store.GlobalInst}
    (stored : store.globals.val = base ++ produced)
    (previous : GlobalSourceValues sourceStore sourceInstance sources produced)
    (success : status = .Ok ()) :
    ∃ values, after.globals.val = base ++ values ∧
      GlobalSourceValues sourceStore sourceInstance (sources ++ [original]) values := by
  cases effect with
  | failed error => simp at success
  | appended globals addresses lo hi entries mapped canonical room decoded =>
    refine ⟨produced ++ [{ty := original.gtype, lo := lo, hi := hi}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using entries
    · apply List.rel_append previous
      exact .cons ⟨rfl, by simpa only [decodeGlobal, decoded] using evaluated⟩ .nil
end Itasca.Runtime.Store

end
