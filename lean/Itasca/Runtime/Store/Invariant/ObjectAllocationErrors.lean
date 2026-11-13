import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Preparation.PreparationErrorLoops
import Itasca.Runtime.Store.Preparation.PreparationResults
import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Store.Initialization.ElementSourceStaging
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Api.MemoryAllocationLoop
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend

/-!
Sections, each formerly its own module: AllocatedDataLoop, AllocatedElementLoop, AllocatedGlobalLoop, ObjectAllocationErrors.
-/

/-! ## AllocatedDataLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem data_allocated_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (matching : ElementTypeMap store inst.module.module.env.elements.val inst.elems.val)
    (contents : ElementContents store)
    (issued : ∀ address ∈ inst.datas.val, address.val < store.datas.length) :
    runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ AllocationShape view after ∧ ElementContents after ∧ after.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          (∀ address ∈ next.datas.val, address.val < after.datas.length) ∧ next.globals = inst.globals ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          ElementTypeMap after inst.module.module.env.elements.val next.elems.val ∧
          (finalStatus = .Ok () → next.datas.length = inst.datas.length + (inst.module.module.tail.data.val.length - start.val)) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state => StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧ ElementContents state.1 ∧ state.1.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        (∀ address ∈ currentInst.datas.val, address.val < state.1.datas.length) ∧ currentInst.globals = inst.globals ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        ElementTypeMap state.1 inst.module.module.env.elements.val currentInst.elems.val ∧
        (state.2.1 = .Ok () → currentInst.datas.length + start.val = inst.datas.length + state.2.2.val))
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, hcapacity, hstoreCapacity, htyped, hcount⟩
    dsimp only at hstaged hobjects hallocated hcontents hglobals haccounted hmetadata hindex hfound hsource hissued hglobalMap hbindings himports hsegments hcapacity hstoreCapacity htyped hcount ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.metadata.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata,
          currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, htyped, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
        step with add_instance_data_result_effect memory allocator law current instIndex index currentInst
          hfound (by simpa only [hsource] using hmore) room mapRoom
          as ⟨state, after, resultEffect⟩
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, effect.allocated hallocated, effect.contents hcontents, effect.globals.trans hglobals, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.addresses hfound nextFound hissued, (effect.global_map hfound nextFound).trans hglobalMap, nextBindings, nextImports, nextSegments, ?_, ?_,
          effect.element_types hfound nextFound htyped, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          have nextCount := resultEffect.count (List.getElem?_eq_some_iff.mp hfound).1 nextFound success
          have oldCount := hcount rfl
          omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.tail.data.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata,
        currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, htyped, fun success => by have counted := hcount success; omega⟩
  · exact ⟨staged, objectBound, allocated, contents, rfl, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, issued, rfl, bindings, imports, segments, mapCapacity, storeCapacity, matching, fun _ => by simp⟩

end Itasca.Runtime.Store

end

/-! ## AllocatedElementLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem element_allocated_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
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
    (allocated : AllocationShape view store)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (matching : status = .Ok () → ElementTypeMap store (inst.module.module.env.elements.val.take start.val) inst.elems.val)
    (contents : ElementContents store) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ AllocationShape view after ∧ ElementContents after ∧ after.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧ next.globals = inst.globals ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → ElementTypeMap after inst.module.module.env.elements.val next.elems.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧ ElementContents state.1 ∧ state.1.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧ currentInst.globals = inst.globals ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → ElementTypeMap state.1 (inst.module.module.env.elements.val.take state.2.2.2.val) currentInst.elems.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, htyped⟩
    dsimp only at hhost hstaged hobjects hallocated hcontents hglobals haccounted hmetadata hindex hfound hsource hglobalMap hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData htyped ⊢
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
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata,
          currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hdatas, hmapData, by simp⟩
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
        step with add_instance_element_content_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings room mapRoom
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
        refine ⟨nextStaged, nextObjects, contentEffect.allocated hallocated, contentEffect.contents hcontents, effect.globals.trans hglobals, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, (effect.global_map hfound nextFound).trans hglobalMap, nextBindings, nextImports, nextSegments, ?_,
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
      exact ⟨current, result, rfl, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata,
        currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hdatas, hmapData, fun success => by simpa only [atEnd, List.take_length] using htyped success⟩
  · exact ⟨rfl, staged, objectBound, allocated, contents, rfl, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, matching⟩

end Itasca.Runtime.Store

end

/-! ## AllocatedGlobalLoop -/

section

/-! The actual staged global loop preserves pre-existing store objects and the
linked initializer context through all allocation/refusal branches. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem global_allocated_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max)
    (issued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ AllocationShape view after ∧ GlobalContents after ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          (∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length) ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → next.globals.length = inst.globals.length + (inst.module.module.env.globals.val.length - start.val)) ⦄ := by
  have contents : GlobalContents store := bindings.globals
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧ GlobalContents state.1 ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        (∀ address ∈ currentInst.globals.val, address.store = state.1.id ∧ address.index.val < state.1.globals.length) ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → currentInst.globals.length + start.val = inst.globals.length + state.2.2.2.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hallocated, hcontents, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hissued, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData, hcount⟩
    dsimp only at hhost hstaged hobjects hallocated hcontents haccounted hmetadata hindex hfound hsource hissued hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData hcount ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hallocated, hcontents, haccounted, hmetadata,
          currentInst, hfound, hsource, hissued, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        step with add_instance_global_result_effect memory hooks floats allocator law current platform instIndex index
          currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room
          as ⟨state, after, host', resultEffect, hhost'⟩
        subst host'
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, effect.allocated hallocated, effect.contents hcontents, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.addresses hfound nextFound hissued, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · intro success
          have nextCount := resultEffect.count (List.getElem?_eq_some_iff.mp hfound).1 nextFound success
          have oldCount := hcount rfl
          omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.env.globals.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hallocated, hcontents, haccounted, hmetadata,
        currentInst, hfound, hsource, hissued, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, fun success => by have counted := hcount success; omega⟩
  · exact ⟨rfl, staged, objectBound, allocated, contents, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, issued, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl, fun _ => by simp⟩

end Itasca.Runtime.Store

end

/-! ## ObjectAllocationErrors -/

section

/-!
Object allocation error classification through staging loops. Shared certificates remain independent of the instantiation construction.
-/

/-! ## Object Allocation Errors -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem add_table_errors_metadata {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.wasm_types.TableType)
    (found : inst.module.module.env.table_types.val[index.val]? = some ty)
    (fit : LimitsFit ty.limits core.num.U32.MAX)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_table memory allocator store inst index = .ok out) :
    ErrorAllowed ResourceError out.1 ∧ out.2.2.module = inst.module := by
  unfold runtime.store.instantiate.Store.add_instance_table at run
  simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.table_types.deref index ty (by simpa [alloc.vec.Vec.deref] using found)] at run
  simp only [bind_ok] at run
  obtain ⟨⟨status, after⟩, defined, rest⟩ := normal_bind_exists _ _ _ run
  have cause := define_table_errors memory allocator law store ty fit _ defined
  clear run
  rename' rest => run
  repeat' allocation_error_step run using allocator, law

theorem add_memory_errors_metadata {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (ty : Itasca.wasm_types.MemType)
    (found : inst.module.module.env.mem_types.val[index.val]? = some ty)
    (fit : LimitsFit ty.limits 65536#u32)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_memory memory allocator store inst index = .ok out) :
    ErrorAllowed ResourceError out.1 ∧ out.2.2.module = inst.module := by
  have multiply : (UScalar.cast .U64 ty.limits.min) * 65536#u64
      ⦃ size => size.val = ty.limits.min.val * 65536 ⦄ := by
    step as ⟨size, sizeValue⟩
    scalar_tac
  obtain ⟨size, sizeRun, sizeValue⟩ := WP.spec_imp_exists multiply
  unfold runtime.store.instantiate.Store.add_instance_memory at run
  simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.mem_types.deref index ty (by simpa [alloc.vec.Vec.deref] using found)] at run
  simp only [bind_ok,
    lift, sizeRun] at run
  split at run
  · repeat' allocation_error_step run using allocator, law
  · rename_i fits
    have bounded : size.val ≤ Usize.max := by scalar_tac
    have castExact := cast_usize_exact size bounded
    obtain ⟨buffer, createRun, zeroes⟩ := WP.spec_imp_exists (laws.create (UScalar.cast .Usize size))
    simp only [createRun] at run
    cases buffer with
    | none => repeat' allocation_error_step run using allocator, law
    | some buffer =>
      have length : (view buffer).length = ty.limits.min.val * 65536 := by
        have contents := zeroes buffer rfl
        have lengths := congrArg List.length contents
        simpa [castExact, sizeValue] using lengths
      simp only [bind_ok] at run
      obtain ⟨within, withinRun, rest⟩ := normal_bind_exists _ _ _ run
      clear run
      rename' rest => run
      split at run
      · obtain ⟨⟨status, after⟩, defined, rest⟩ := normal_bind_exists _ _ _ run
        have cause := define_memory_errors memory allocator law view laws store ty buffer fit length _ defined
        clear run
        rename' rest => run
        repeat' allocation_error_step run using allocator, law
      · repeat' allocation_error_step run using allocator, law

end Itasca.Runtime.Store

end

/-! ## Object Allocation Error Loops -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
theorem table_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (fits : ∀ ty ∈ inst.module.module.env.table_types.val, LimitsFit ty.limits core.num.U32.MAX)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator store status index inst = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop5 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop5.body,
      runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, bind_ok] at run
    split at run
    · rename_i more
      have indexBound : index.val < inst.module.module.env.table_types.length := by simpa [alloc.vec.Vec.deref] using more
      let ty := inst.module.module.env.table_types.val[index.val]
      have found : inst.module.module.env.table_types.val[index.val]? = some ty := List.getElem?_eq_getElem indexBound
      have fit := fits ty (List.getElem_mem indexBound)
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have ⟨nextAllowed, sameModule⟩ := add_table_errors_metadata memory allocator law store inst index ty found fit _ called
        change nextInst.module = inst.module at sameModule
        have nextFits : ∀ ty ∈ nextInst.module.module.env.table_types.val, LimitsFit ty.limits core.num.U32.MAX := by simpa only [sameModule] using fits
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator nextStore nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop5, runtime.store.instantiate.Store.prepare_instance_loop5.body,
            runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.table_types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextFits nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

theorem memory_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (fits : ∀ ty ∈ inst.module.module.env.mem_types.val, LimitsFit ty.limits 65536#u32)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store status index inst = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop6 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop6.body,
      runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, bind_ok] at run
    split at run
    · rename_i more
      have indexBound : index.val < inst.module.module.env.mem_types.length := by simpa [alloc.vec.Vec.deref] using more
      let ty := inst.module.module.env.mem_types.val[index.val]
      have found : inst.module.module.env.mem_types.val[index.val]? = some ty := List.getElem?_eq_getElem indexBound
      have fit := fits ty (List.getElem_mem indexBound)
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have ⟨nextAllowed, sameModule⟩ := add_memory_errors_metadata memory allocator law view laws store inst index ty found fit _ called
        change nextInst.module = inst.module at sameModule
        have nextFits : ∀ ty ∈ nextInst.module.module.env.mem_types.val, LimitsFit ty.limits 65536#u32 := by simpa only [sameModule] using fits
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator nextStore nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop6, runtime.store.instantiate.Store.prepare_instance_loop6.body,
            runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextFits nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

end Itasca.Runtime.Store

end

end
