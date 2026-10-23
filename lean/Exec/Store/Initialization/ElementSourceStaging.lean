import Exec.Store.Initialization.SegmentGlobalMetadata
import Exec.Store.Initialization.ElementValueSource
import Exec.Store.Initialization.InitializerMetadata
import Exec.Store.Initialization.ElementEffects

namespace Exec.Store
open Aeneas Aeneas.Std

theorem element_source_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Code.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (sourceContext : InitializerSourceContext sourceStore sourceInstance store inst)
    (baseElements : List runtime.store.ElemInst)
    (matching : status = .Ok () → ∃ produced, store.elems.val = baseElements ++ produced ∧
      ElementSourceSegments sourceStore sourceInstance
        (inst.module.module.env.elements.val.take start.val) produced) :
    runtime.store.instantiate.Store.instantiate_inner_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧ after.globals = store.globals ∧ next.globals = inst.globals ∧
          InitializerSourceContext sourceStore sourceInstance after next ∧
          (finalStatus = .Ok () → ∃ produced, after.elems.val = baseElements ++ produced ∧
            ElementSourceSegments sourceStore sourceInstance inst.module.module.env.elements.val produced) ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧ state.1.globals = store.globals ∧ currentInst.globals = inst.globals ∧
        InitializerSourceContext sourceStore sourceInstance state.1 currentInst ∧
        (state.2.2.1 = .Ok () → ∃ produced, state.1.elems.val = baseElements ++ produced ∧
          ElementSourceSegments sourceStore sourceInstance
            (inst.module.module.env.elements.val.take state.2.2.2.val) produced))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, hglobals, hglobalMap, hcontext, hmatching⟩
    dsimp only at hhost hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData hglobals hglobalMap hcontext hmatching ⊢
    subst host
    unfold runtime.store.instantiate.Store.instantiate_inner_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env, module.Module.env,
      Itasca.module.Module.impl.env, module.Env.elements, Itasca.module.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, hglobals, hglobalMap, hcontext, by simp⟩
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
        step with add_instance_element_value_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings room mapRoom
          sourceStore sourceInstance storeWf frameWf hcontext
          (by
            have sameType : Itasca.ModuleConstants.referenceValueType segment.elem = elementValueType segment.elem := by
              cases segment.elem <;> rfl
            simpa only [sameType] using hvalid.2)
          as ⟨state, after, host', valueEffect, hhost'⟩
        have effect := valueEffect.content.typed.effect
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData, effect.globals.trans hglobals, (effect.global_map hfound nextFound).trans hglobalMap, effect.source_context hfound nextFound hcontext, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          obtain ⟨produced, stored, previous⟩ := hmatching rfl
          obtain ⟨values, storedNext, nextValues⟩ := valueEffect.source_values stored previous success
          refine ⟨values, storedNext, ?_⟩
          rw [hnext, List.take_succ_eq_append_getElem hmore]
          exact nextValues
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.elements.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, hglobals, hglobalMap, hcontext, ?_⟩
      simpa only [atEnd, List.take_length] using hmatching
  · exact ⟨rfl, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, rfl, rfl, sourceContext, matching⟩

end Exec.Store
