import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Initialization.ElementEffects
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Initialization.ElementTypedEffect
import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.ElementTypes

/-!
Element allocation bounds and staging-loop preservation. The bounded effect retains typed segment contents and supplies the loop certificate used by preparation.
-/

/-! ## Element Bounded Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact element staging retains the source reference type in the newly
allocated segment and distinguishes a normal refusal from successful append. -/
inductive ElementBoundedEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) (source : Itasca.metadata.Element) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementBoundedEffect store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len])
      (bounded : values.length < 2^32) :
      ElementBoundedEffect store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementBoundedEffect.bounds {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (effect : ElementBoundedEffect store instIndex inst source status after)
    (before : SegmentBounds store) : SegmentBounds after := by
  cases effect with
  | failed error => exact before
  | appended elements addresses values stored mapped bounded =>
    constructor
    · intro element member
      simp only [stored, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact before.elements element old
      · exact bounded
    · exact before.data

theorem ElementBoundedEffect.typed {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (effect : ElementBoundedEffect store instIndex inst source status after) :
    ElementTypedEffect store instIndex inst source status after := by
  cases effect with
  | failed error => exact .failed error
  | appended elements addresses values stored mapped bounded => exact .appended elements addresses _ stored mapped

theorem add_instance_element_bounded_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (sourceBound : segment.init.length < 2^32)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementBoundedEffect store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
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
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementBoundedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
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
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementBoundedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementBoundedEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
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
        have effect := ElementBoundedEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses) (by have n := segment.init.len_val; omega)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)

end Itasca.Runtime.Store

end

/-! ## Element Bounds Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem element_bounds_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (matching : status = .Ok () → ElementTypeMap store (inst.module.module.env.elements.val.take start.val) inst.elems.val)
    (contents : SegmentBounds store)
    (sourceBounds : ∀ segment ∈ inst.module.module.env.elements.val, segment.init.length < 2^32) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ SegmentBounds after ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → ElementTypeMap after inst.module.module.env.elements.val next.elems.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ SegmentBounds state.1 ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → ElementTypeMap state.1 (inst.module.module.env.elements.val.take state.2.2.2.val) currentInst.elems.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hcontents, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, htyped⟩
    dsimp only at hhost hstaged hobjects hcontents haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData htyped ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hcontents, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let segment := inst.module.module.env.elements.val[index.val]
        have hsegment : currentInst.module.module.env.elements.val[index.val]? = some segment := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleSegments.elementValid currentInst.module.module.env segment := by
          rw [hsource]
          exact valid segment (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        have certificates := element_initializer_certificates current currentInst index segment
          (by simpa [hsource] using compiled) hsegment hvalid hbindings himports
        have room : current.elems.length < Usize.max := by omega
        have mapRoom : currentInst.elems.length < Usize.max := by omega
        step with add_instance_element_bounded_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings
          (sourceBounds segment (List.getElem_mem hmore)) room mapRoom
          as ⟨state, after, host', contentEffect, hhost'⟩
        subst host'
        have typedEffect := contentEffect.typed
        have effect := typedEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, contentEffect.bounds hcontents, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          have typed := typedEffect.type_map (List.getElem?_eq_some_iff.mp hfound).1 nextFound (htyped rfl) success
          simpa only [hnext, List.take_succ_eq_append_getElem hmore] using typed
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.elements.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hcontents, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, fun success => by simpa only [atEnd, List.take_length] using htyped success⟩
  · exact ⟨rfl, staged, objectBound, contents, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, matching⟩

end Itasca.Runtime.Store

end
