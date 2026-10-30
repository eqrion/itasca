import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Initialization.ElementSourceLoop
import Itasca.Runtime.Store.Initialization.ElementContentEffect

/-!
Allocated element values and their decoded source-segment relation. Typed content and loop shape remain lower certificates used independently by initialization.
-/

/-! ## Element Value Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

inductive ElementValueEffect {M : Type} (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (store : runtime.store.Store M) (instIndex : Usize) (inst : runtime.store.ModuleInst)
    (source : Itasca.metadata.Element) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementValueEffect sourceStore sourceInstance store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len])
      (canonical : ∀ word ∈ values.val, ReferenceShape store source.elem word)
      (evaluated : ElementSourceValues sourceStore sourceInstance source.elem source.init.val values.val) :
      ElementValueEffect sourceStore sourceInstance store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementValueEffect.content {M : Type} {sourceStore sourceInstance}
    {store after : runtime.store.Store M} {instIndex inst source status}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst source status after) :
    ElementContentEffect store instIndex inst source status after := by
  cases effect with
  | failed error => exact .failed error
  | appended elements addresses values stored mapped canonical evaluated =>
    exact .appended elements addresses values stored mapped canonical

theorem add_instance_element_value_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ∀ expr ∈ segment.init.val,
      Itasca.ModuleConstants.Valid inst.module.module.env expr (elementValueType segment.elem)) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementValueEffect sourceStore sourceInstance store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_source_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac) (by simp)
      sourceStore sourceInstance storeWf frameWf context valid (by simp [ElementSourceValues])
      as ⟨after, host, values, status, hs, hp, hvalues, refs, evaluated⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
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
        have effect := ElementValueEffect.appended (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses) refs (evaluated rfl)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)


end Itasca.Runtime.Store

end

/-! ## Element Value Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementSourceSegments (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (source : List Itasca.metadata.Element) (values : List runtime.store.ElemInst) : Prop :=
  List.Forall₂ (fun original actual => actual.ty = original.elem ∧
    ElementSourceValues sourceStore sourceInstance original.elem original.init.val actual.refs.val) source values

theorem ElementStageEffect.source_context {M : Type} {store after : runtime.store.Store M}
    {instIndex inst next sourceStore sourceInstance}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (context : InitializerSourceContext sourceStore sourceInstance store inst) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact context
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact ⟨context.functions, context.globals⟩

theorem ElementValueEffect.source_values {M : Type} {store after : runtime.store.Store M}
    {instIndex inst sourceStore sourceInstance status}
    {original : Itasca.metadata.Element}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst original status after)
    {sources : List Itasca.metadata.Element} {base produced : List runtime.store.ElemInst}
    (stored : store.elems.val = base ++ produced)
    (previous : ElementSourceSegments sourceStore sourceInstance sources produced)
    (success : status = .Ok ()) :
    ∃ values, after.elems.val = base ++ values ∧
      ElementSourceSegments sourceStore sourceInstance (sources ++ [original]) values := by
  cases effect with
  | failed error => simp at success
  | appended elements addresses values entries mapped canonical evaluated =>
    refine ⟨produced ++ [{ty := original.elem, refs := values}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using entries
    · exact List.rel_append previous (.cons ⟨rfl, evaluated⟩ .nil)
end Itasca.Runtime.Store

end
