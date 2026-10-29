import Itasca.Runtime.Store.Preparation.AllocationCauses
import Itasca.Runtime.Store.Initialization.Data
import Itasca.Runtime.Store.Invariant.NormalResult
import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappings
import Itasca.Runtime.Store.Initialization.DataStagingLoop
import Itasca.Runtime.Store.Preparation.PreparationCalls

/-!
Data-segment staging resource causes. Byte-copy allocation failures lift through one segment and the staging loop to the complete data allocation cause.
-/

/-! ## Data Allocation Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The only failure in copying a source data payload is the exact initial
byte-vector reservation refusal. -/
theorem copy_bytes_resource_causes {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (source : Slice U8) :
    runtime.store.copy_bytes allocator source ⦃ answer =>
      (answer = .Err (.Exhausted .Allocation) ∧
        allocator.reserve (alloc.vec.Vec.new U8) source.len = .ok (false,alloc.vec.Vec.new U8)) ∨
      ∃ bytes, answer = .Ok bytes ∧ bytes.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes
  dsimp only
  obtain ⟨reserved,wrapped,called⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U8) source.len
  rw [wrapped]
  cases reserved
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,called]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with copy_bytes_loop source (alloc.vec.Vec.new U8) 0#usize (by scalar_tac) (by simp) as ⟨bytes,same⟩
    simp [same]
end Itasca.Runtime.Store

end

/-! ## Data Staging Cause -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Both exact allocation requests made when adding a passive data payload. -/
def DataAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (data : Itasca.module.Data) (error : runtime.ExecError) : Prop :=
  error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U8) data.init.len = .ok (false,alloc.vec.Vec.new U8) ∨
      allocator.reserve store.datas 1#usize = .ok (false,store.datas))

theorem add_data_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instanceIndex index : Usize)
    (inst : runtime.store.ModuleInst) (data : Itasca.module.Data)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (selected : inst.module.module.tail.data.val[index.val]? = some data)
    (error : runtime.ExecError) (after : runtime.store.Store M)
    (run : runtime.store.instantiate.Store.add_instance_data memory allocator store instanceIndex index = .ok (.Err error,after)) :
    after = store ∧ DataAllocationCause allocator store data error := by
  unfold runtime.store.instantiate.Store.add_instance_data at run
  simp only [Compiler.initializer_vec_index store.instances instanceIndex inst found,
    runtime.compiler.ExecutableModule.tail,Itasca.module.Module.impl.tail,bind_ok,
    Compiler.initializer_vec_index inst.module.module.tail.data index data selected] at run
  obtain ⟨copied,copiedRun,effect⟩ := WP.spec_imp_exists (copy_bytes_resource_causes allocator law data.init.deref)
  rw [copiedRun,bind_ok] at run
  rcases effect with ⟨failed,refused⟩ | ⟨bytes,copied,contents⟩
  · subst copied
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl (by simpa [alloc.vec.Vec.deref,alloc.vec.Vec.len,Slice.len] using refused)⟩
  · subst copied
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨answer,reserved,refusal⟩ := reserve_with_cause allocator law store.datas 1#usize
    rw [reserved] at run
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl⟩ := run
      exact ⟨rfl,rfl,Or.inr refusal⟩
    · simp [core.result.Result.Insts.CoreOpsTry.branch] at run
      obtain ⟨datas,pushed,run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
      simp only [uncurry_apply_pair] at run
      obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
      simp at run
end Itasca.Runtime.Store

end

/-! ## Data Staging Causes -/

section

namespace Itasca.Runtime.Store
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
    simp only [runtime.compiler.ExecutableModule.tail,
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

end Itasca.Runtime.Store

end
