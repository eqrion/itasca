import Exec.Representation.Collection
import Exec.Store.Initialization.ElementStaging
import Exec.Store.Api.GlobalEffects

namespace Exec.Store
open Aeneas Aeneas.Std

inductive ElementStageEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.Instance) : runtime.store.Store M → Prop where
  | unchanged : ElementStageEffect store instIndex inst store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInstance)
      (addresses : alloc.vec.Vec Usize) (element : runtime.store.ElemInstance)
      (elementValues : elements.val = store.elems.val ++ [element])
      (addressValues : addresses.val = inst.elements.val ++ [store.elems.len]) :
      ElementStageEffect store instIndex inst
        { store with elems := elements, instances := store.instances.set instIndex { inst with elements := addresses } }

theorem add_instance_element_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elements.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementStageEffect store instIndex inst out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
    Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
  step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac)
      as ⟨after, host, values, status, hs, hp, hvalues⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementStageEffect.unchanged (store := store) (instIndex := instIndex) (inst := inst))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Exec.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementStageEffect.appended (store := store) (instIndex := instIndex) (inst := inst)
          elements addresses {ty := segment.elem, refs := values} helements
          (by simpa only [instanceRead] using haddresses)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)


theorem ElementStageEffect.context {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst) :
    ∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
      InitializerBindings after next ∧ InitializerImports after next ∧
      InitializerSegmentBindings after next ∧ next.elements.length ≤ inst.elements.length + 1 ∧
      after.elems.length ≤ store.elems.length + 1 ∧ next.data = inst.data := by
  cases effect with
  | unchanged => exact ⟨inst, found, rfl, bindings, imports, segments, by omega, by omega, rfl⟩
  | appended elements addresses element elementValues addressValues =>
    have bound : instIndex.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    refine ⟨{inst with elements := addresses}, ?_, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [alloc.vec.Vec.set_val_eq, bound]
    · exact ⟨bindings.funcs, bindings.globals⟩
    · exact imports.extend rfl rfl (by simp) (by simp)
    · exact ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩
    · simp [addressValues]
    · simp [elementValues]

theorem ElementStageEffect.data {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : ElementStageEffect store instIndex inst after) : after.datas = store.datas := by
  cases effect <;> rfl

theorem ElementStageEffect.object_count {M : Type} {store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : ElementStageEffect store instIndex inst after) : objectCount after = objectCount store := by
  cases effect <;> rfl

theorem ElementStageEffect.staged {M : Type} {before store after : runtime.store.Store M}
    {instIndex : Usize} {inst : runtime.store.Instance}
    (effect : ElementStageEffect store instIndex inst after)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val) :
    StagedPrefix before after := by
  cases effect with
  | unchanged => exact staged
  | appended elements addresses element elementValues addressValues =>
    have appended : StagedPrefix store {store with elems := elements} := by
      constructor <;> simp [elementValues]
    exact (staged.trans appended).set_fresh_instance instIndex {inst with elements := addresses} fresh

end Exec.Store
