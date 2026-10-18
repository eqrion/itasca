import Exec.Representation.Collection
import Exec.Store.Initialization.ElementEffects
import Exec.Store.Initialization.SegmentTypes

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Exact element staging retains the source reference type in the newly
allocated segment and distinguishes a normal refusal from successful append. -/
inductive ElementTypedEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.Instance) (source : Itasca.module.Element) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementTypedEffect store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInstance) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elements.val ++ [store.elems.len]) :
      ElementTypedEffect store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elements := addresses}}

theorem ElementTypedEffect.effect {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (typed : ElementTypedEffect store instIndex inst source status after) :
    ElementStageEffect store instIndex inst after := by
  cases typed with
  | failed error => exact .unchanged
  | appended elements addresses values stored mapped => exact .appended elements addresses _ stored mapped

theorem add_instance_element_typed_effect {M P F A : Type}
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
      ⦃ out => ElementTypedEffect store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
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
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementTypedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
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
        have effect := ElementTypedEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)


end Exec.Store
