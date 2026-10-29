import Itasca.Runtime.Store.Initialization.DataStagingLoop
import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Api.GlobalLoop
import Itasca.Runtime.Store.Initialization.SegmentBoundsEffects
import Itasca.Runtime.Store.Initialization.SegmentInstructionShape
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Initialization.ElementContentEffect
import Itasca.Runtime.Store.Invariant.AddressOrder
import Itasca.Runtime.Store.Initialization.DataValueMetadata

/-!
Data-segment allocation-loop bounds, content, ordering and payload. The construction is used before returning the resolved start handle; it does not invoke the start function.
-/

/-! ## Data Bounds Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem data_bounds_staging_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (bounded : SegmentBounds store)
    (sourceBounds : ∀ data ∈ inst.module.module.tail.data.val, data.init.length < 2^32) :
    runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ SegmentBounds after ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ InitializerContext after instIndex inst.module ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state => StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ SegmentBounds state.1 ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max)
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, hbounded, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity⟩
    dsimp only at hstaged hobjects hbounded haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hbounded, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
        step with segment_specs_and
          (add_instance_data_stage_effect memory allocator law current instIndex index currentInst
            hfound (by simpa only [hsource] using hmore) room mapRoom)
          (add_instance_data_bounds memory allocator law current instIndex index currentInst
            hfound (by simpa only [hsource] using hmore) room mapRoom
            (by simpa only [hsource] using sourceBounds) hbounded)
          as ⟨state, after, effect, nextBounds⟩
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, nextBounds, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hbounded, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments⟩
  · exact ⟨staged, objectBound, bounded, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity⟩

end Itasca.Runtime.Store

end

/-! ## Data Content Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem DataStageEffect.contents {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after)
    (contents : ElementContents store) : ElementContents after := by
  cases effect with
  | unchanged => exact contents
  | appended datas addresses data stored mapped => simpa only [ElementContents, ReferenceShape] using contents

end Itasca.Runtime.Store

end

/-! ## Data Order Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem data_order_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (base : Nat) (initial : List Nat)
    (ordered : AddressOrder base initial store.datas.length (inst.datas.val.map (UScalar.val))) :
    runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ (∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          AddressOrder base initial after.datas.length (next.datas.val.map (UScalar.val)) ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state => StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        AddressOrder base initial state.1.datas.length (currentInst.datas.val.map (UScalar.val)) ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max)
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, horder, hbindings, himports, hsegments, hcapacity, hstoreCapacity⟩
    dsimp only at hstaged hobjects haccounted hmetadata hindex hfound hsource horder hbindings himports hsegments hcapacity hstoreCapacity ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, horder, hbindings, himports, hsegments⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
        step with add_instance_data_stage_effect memory allocator law current instIndex index currentInst
          hfound (by simpa only [hsource] using hmore) room mapRoom
          as ⟨state, after, effect⟩
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.address_order hfound nextFound horder, nextBindings, nextImports, nextSegments, ?_, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, horder, hbindings, himports, hsegments⟩
  · exact ⟨staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, ordered, bindings, imports, segments, mapCapacity, storeCapacity⟩

end Itasca.Runtime.Store

end

/-! ## Data Payload Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem data_payload_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (initial : List datainst)
    (payload : status = .Ok () → store.datas.val.map decodeData = initial ++
      (inst.module.module.tail.data.val.take start.val).map sourceDataPayload) :
    runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ (∃ next, after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ next.elems = inst.elems ∧ after.globals = store.globals ∧ next.globals = inst.globals) ∧
        (finalStatus = .Ok () → after.datas.val.map decodeData = initial ++
          inst.module.module.tail.data.val.map sourceDataPayload) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state => StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      (state.2.1 = .Ok () → state.1.datas.val.map decodeData = initial ++
        (inst.module.module.tail.data.val.take state.2.2.val).map sourceDataPayload) ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ currentInst.elems = inst.elems ∧
        state.1.globals = store.globals ∧ currentInst.globals = inst.globals)
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, haccounted, hmetadata, hindex, hpayload,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, helems, helemMap, hglobals, hglobalMap⟩
    dsimp only at hstaged hobjects haccounted hmetadata hindex hpayload hfound hsource hbindings himports hsegments hcapacity hstoreCapacity helems helemMap hglobals hglobalMap ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          ⟨currentInst, hfound, hsource, hbindings, himports, hsegments, helems, helemMap, hglobals, hglobalMap⟩, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
        step with add_instance_data_payload memory allocator law current instIndex index currentInst
          hfound (by simpa only [hsource] using hmore) room mapRoom
          as ⟨state, after, resultEffect, nextPayload⟩
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_, ?_,
          effect.elements.trans helems, (effect.element_map hfound nextFound).trans helemMap,
          effect.globals.trans hglobals, (effect.global_map hfound nextFound).trans hglobalMap⟩, ?_⟩
        · omega
        · intro success
          rw [nextPayload success, hpayload rfl, hnext,
            List.take_succ_eq_append_getElem hmore, List.map_append, List.map_cons, List.map_nil,
            List.append_assoc]
          simp only [hsource]
        · omega
        · omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.tail.data.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        ⟨currentInst, hfound, hsource, hbindings, himports, hsegments, helems, helemMap, hglobals, hglobalMap⟩, ?_⟩
      intro success
      simpa only [endIndex, List.take_length] using hpayload success
  · exact ⟨staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, payload, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, rfl, rfl⟩

end Itasca.Runtime.Store

end
