import Itasca.Runtime.Store.Initialization.DataStagingLoop
import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Api.GlobalLoop
import Itasca.Runtime.Store.Initialization.SegmentBoundsEffects
import Itasca.Runtime.Store.Initialization.SegmentInstructionShape

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
