import Exec.Store.Initialization.DataStagingLoop
import Exec.Store.Initialization.DataStagingCause
import Exec.Store.Preparation.PreparationCalls
namespace Exec.Store
open Aeneas Aeneas.Std

abbrev dataStageCall {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (instIndex : Usize)
    (store : runtime.store.Store M) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index

def DataStagingCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M)
    (instIndex start : Usize) (error : runtime.ExecError) : Prop :=
  ∃ current index inst data,
    PreparationCalls (dataStageCall memory allocator instIndex) store start current index ∧
    current.instances.val[instIndex.val]? = some inst ∧
    inst.module.module.tail.data.val[index.val]? = some data ∧
    runtime.store.instantiate.Store.add_instance_data memory allocator current instIndex index = .ok (.Err error,current) ∧
    DataAllocationCause allocator current data error

theorem data_staging_resource_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator store (.Ok ()) start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧
        (∀ error, finalStatus = .Err error → DataStagingCause memory allocator store instIndex start error) ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ InitializerContext after instIndex inst.module ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state =>
      (state.2.1 = .Ok () → PreparationCalls (dataStageCall memory allocator instIndex) store start state.1 state.2.2) ∧
      (∀ error, state.2.1 = .Err error → DataStagingCause memory allocator store instIndex start error) ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max)
  · rintro ⟨current, result, index⟩ ⟨trace, causes, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity⟩
    dsimp only at hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail,
      Itasca.module.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, causes, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
        have reached := trace rfl
        obtain ⟨⟨state,after⟩,called,effect⟩ := WP.spec_imp_exists
          (add_instance_data_stage_effect memory allocator law current instIndex index currentInst
            hfound (by simpa only [hsource] using hmore) room mapRoom)
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        dsimp only at nextStoreSize nextSize
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨?_,?_,nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_, ?_⟩, ?_⟩
        · intro success
          subst state
          exact .next reached called hnext
        · intro error rejected
          subst state
          let data := inst.module.module.tail.data.val[index.val]
          have selected : currentInst.module.module.tail.data.val[index.val]? = some data := by
            rw [hsource]
            exact List.getElem?_eq_getElem hmore
          obtain ⟨same,cause⟩ := add_data_resource_cause memory allocator law current instIndex index currentInst data hfound selected error after called
          subst after
          exact ⟨current,index,currentInst,data,reached,hfound,selected,called,cause⟩
        · omega
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, causes, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments⟩
  · exact ⟨(fun _ => .refl _ _), (by simp), staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity⟩

end Exec.Store
