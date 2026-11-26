import Itasca.Runtime.Store.Preparation.ResourceBounds
import Itasca.Runtime.Store.Definitions
import Itasca.Generated.Funs
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Invariant.FunctionAndTypeStagingCauses
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Store.Initialization.SegmentLoops
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Api.AllocationAndGrowth
import Itasca.Runtime.Store.Api.TableAndGlobalAllocation
import Itasca.Runtime.Store.Linking.LinkLoop
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Store.Invariant.SourceAllocationLists
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Preparation.PreparationErrorLoops
import Itasca.Runtime.Store.Invariant.ObjectAllocationErrors
import Itasca.Runtime.Store.Api.AllocationLoops
import Itasca.Runtime.Equations.Interp

/-!
Proofs for Runtime / Store / Instantiation.

This module collects SegmentStagingCauses, TailCommit.
Each section documents its contracts and consumers.
-/

/-! ## SegmentStagingCauses -/

section

/-!
# Segment Staging Causes

Element and data staging identify the concrete resource causes used by initialization outcomes.
-/

/-! ## DataStagingCauses -/

section

/-!
Data-segment staging resource causes. Byte-copy allocation failures lift through one segment and the staging loop to the complete data allocation cause.
-/

/-! ## Data Allocation Causes -/

section

namespace Itasca.Store
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
end Itasca.Store

end

/-! ## Data Staging Cause -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem add_data_resource_cause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instanceIndex index : Usize)
    (inst : runtime.store.ModuleInst) (data : Itasca.metadata.Data)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (selected : inst.module.module.tail.data.val[index.val]? = some data)
    (error : runtime.ExecError) (after : runtime.store.Store M)
    (run : runtime.store.instantiate.Store.add_instance_data memory allocator store instanceIndex index = .ok (.Err error,after)) :
    after = store ∧ DataAllocationCause allocator store data error := by
  unfold runtime.store.instantiate.Store.add_instance_data at run
  simp only [Compiler.initializer_vec_index store.instances instanceIndex inst found,
    runtime.compiler.ExecutableModule.tail.eq,Itasca.metadata.Module.impl.tail,bind_ok,
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
end Itasca.Store

end

/-! ## Data Staging Causes -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

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
        StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ PreparationGrowth store after {} ∧ after.elems = store.elems ∧
        after.datas.length ≤ store.datas.length + inst.module.module.tail.data.length ∧
        (∀ error, finalStatus = .Err error → ∃ item ∈ inst.module.module.tail.data.val,
          DataAllocationCause allocator after item error) ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ InitializerContext after instIndex inst.module ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state =>
      StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ PreparationGrowth store state.1 {} ∧ state.1.elems = store.elems ∧
      state.1.datas.length ≤ store.datas.length + state.2.2.val ∧
      (∀ error, state.2.1 = .Err error → ∃ item ∈ inst.module.module.tail.data.val,
        DataAllocationCause allocator state.1 item error) ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max)
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, hgrowth, helements, hlength, localCause, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity⟩
    dsimp only at hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail.eq,
      Itasca.metadata.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hgrowth, helements, (by dsimp only [alloc.vec.Vec.length] at hlength hindex ⊢; omega), localCause, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.datas.length < Usize.max := by omega
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
        -- Segment bookkeeping consumes no additional quota-counted objects,
        -- signature values, linear-memory bytes, or table elements.
        have nextGrowth : PreparationGrowth store after {} := by
          cases effect <;> exact ⟨hgrowth.limits, hgrowth.objects, hgrowth.signatures, hgrowth.memoryBytes, hgrowth.tableElements⟩
        have nextElements : after.elems = store.elems := by cases effect <;> exact helements
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, nextGrowth, nextElements, ?_, ?_, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_, ?_⟩, ?_⟩
        · dsimp only at hlength
          omega
        · intro error rejected
          subst state
          let data := inst.module.module.tail.data.val[index.val]
          have selected : currentInst.module.module.tail.data.val[index.val]? = some data := by
            rw [hsource]
            exact List.getElem?_eq_getElem hmore
          obtain ⟨same, cause⟩ := add_data_resource_cause memory allocator law current instIndex index currentInst data hfound selected error after called
          exact ⟨data, List.getElem_mem hmore, by simpa only [same] using cause⟩
        · omega
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hgrowth, helements, (by dsimp only [alloc.vec.Vec.length] at hlength hindex ⊢; omega), localCause, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments⟩
  · exact ⟨staged, objectBound, .refl _, rfl, (by dsimp; omega), (by intro error impossible; cases impossible), (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity⟩

end Itasca.Store

end

end

/-! ## ElementStagingCauses -/

section

/-!
Element-segment staging resource causes. Initializer-loop failures and element allocation requests assemble the resource classification for the complete staging loop.
-/

/-! ## Element Value Causes -/

section

/-! Finite preparation of element initializer values. Each input certificate
connects an actual source expression and retained synthetic function; no
execution premise is accepted. The loop leaves the store and platform intact. -/
namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem elem_value_type_eq (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

private theorem encode_push {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (owned : ValueInStore store value)
    (room : values.length < Usize.max) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ⦄ := by
  step with Representation.encode_value_spec value store.id owned.1 as ⟨pair, hencoded⟩
  rcases pair with ⟨lo, high⟩
  step as ⟨next, hnext⟩
  simp [alloc.vec.Vec.length, hnext]

theorem element_initializers_loop_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index length : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (hlength : length.val = segment.init.length)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (values : alloc.vec.Vec U64) (j : Usize) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed (ElementInitializerCause allocator store inst index segment) status)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧ ErrorAllowed (ElementInitializerCause allocator store inst index segment) out.2.2.2 ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      ErrorAllowed (ElementInitializerCause allocator store inst index segment) p.2.2.2.2)
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, hallowed⟩
    dsimp only at hcurrent hhost hvals hk hallowed ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok, hallowed]
        omega
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨functions, mapping, certificates⟩ := certificates
        obtain ⟨expr, function, code, words, hexpr, hfunction, hcode, compiled, resolved⟩ :=
          certificates k (by omega)
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given inst.module.element_initializers index functions mapping
          as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given functions k function hfunction as ⟨found, hfound⟩
        subst found
        simp only [runtime.compiler.ExecutableModule.env.eq,
          Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
        step with Itasca.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        rw [elem_value_type_eq, bind_ok]
        step with eval_const_owned_resource_causes memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          as ⟨result, after, host', hs, hp, hvalue, errors⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧ ErrorAllowed (ElementInitializerCause allocator store inst index segment) (.Err error) ∧ length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, ⟨k,functions,function,code,expr,by omega,mapping,hfunction,hexpr,hcode,compiled,errors error rfl⟩, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push store vals value owned room)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus⟩
          dsimp only at hstatus
          subst nextStatus
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, True.intro, by omega⟩
          rw [hpush]
          change vals.val.length + 1 ≤ next.val
          omega
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ ErrorAllowed (ElementInitializerCause allocator store inst index segment) state
      exact ⟨by omega, hallowed⟩
  · exact ⟨rfl, rfl, hvalues, hj, allowed⟩

end Itasca.Store

end

/-! ## Element Allocation Causes -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192

theorem add_element_resource_cause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (found : store.instances.val[instIndex.val]? = some inst)
    (element : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (error : runtime.ExecError) (after : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index = .ok (.Err error,after,host)) :
    after = store ∧ host = platform ∧ ElementAllocationCause allocator store inst index segment error := by
  unfold runtime.store.instantiate.Store.add_instance_element at run
  simp only [Compiler.initializer_vec_index store.instances instIndex inst found,
    runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using element)] at run
  obtain ⟨reserved, reserveRun,refusal⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U64) segment.init.len
  simp only [bind_ok, reserveRun] at run
  cases reserved with
  | false =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inl refusal⟩⟩
  | true =>
    simp only [↓reduceIte,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨⟨evaluated,finalHost,values,status⟩,loopRun,sameStore,sameHost,bound,errors⟩ := WP.spec_imp_exists
      (element_initializers_loop_causes memory hooks floats allocator law store platform instIndex index
        segment.init.len inst segment found element (by simp) certificates bindings
        (alloc.vec.Vec.new U64) 0#usize (.Ok ()) True.intro (by simp) (by scalar_tac))
    dsimp only at sameStore sameHost bound errors
    subst evaluated finalHost
    rw [loopRun] at run
    simp only [bind_ok,uncurry_apply_pair] at run
    cases status with
    | Err rejected =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      exact ⟨rfl,rfl,Or.inr errors⟩
    | Ok done =>
      cases done
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
      obtain ⟨answer,reserved,refused⟩ := reserve_with_cause allocator law store.elems 1#usize
      rw [reserved] at run
      cases answer
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inr refused⟩⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements] at run
        obtain ⟨current,read,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨declared,read,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨elements,pushed,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair] at run
        obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
        simp at run
end Itasca.Store

end

/-! ## Element Staging Causes -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem element_staging_resource_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform (.Ok ()) start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧
        ErrorAllowed ResourceError finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ PreparationGrowth store after {} ∧
        after.elems.length ≤ store.elems.length + inst.module.module.env.elements.length ∧
        (∀ error, finalStatus = .Err error → ∃ item ∈ inst.module.module.env.elements.val,
          ElementPreparationResource allocator after item error) ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧
      ErrorAllowed ResourceError state.2.2.1 ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ PreparationGrowth store state.1 {} ∧
      state.1.elems.length ≤ store.elems.length + state.2.2.2.val ∧
      (∀ error, state.2.2.1 = .Err error → ∃ item ∈ inst.module.module.env.elements.val,
        ElementPreparationResource allocator state.1 item error) ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas)
  · rintro ⟨current, host, result, index⟩ ⟨hhost, errors, hstaged, hobjects, hgrowth, hlength, localCause, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData⟩
    dsimp only at hhost errors hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env.eq,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, errors, hstaged, hobjects, hgrowth, (by dsimp only [alloc.vec.Vec.length] at hlength hindex ⊢; omega), localCause, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let segment := inst.module.module.env.elements.val[index.val]
        have hsegment : currentInst.module.module.env.elements.val[index.val]? = some segment := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.Module.Segments.elementValid currentInst.module.module.env segment := by
          rw [hsource]
          exact valid segment (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        have certificates := element_initializer_certificates current currentInst index segment
          (by simpa [hsource] using compiled) hsegment hvalid hbindings himports
        have room : current.elems.length < Usize.max := by omega
        have mapRoom : currentInst.elems.length < Usize.max := by omega
        obtain ⟨⟨state,after,host'⟩,called,⟨effect,hhost'⟩,nextErrors⟩ := WP.spec_imp_exists (normal_return_post
          (add_instance_element_effect memory hooks floats allocator law current platform instIndex index
            currentInst segment hfound hsegment certificates hbindings room mapRoom)
          (fun out called => add_element_errors memory hooks floats allocator law current platform instIndex index
            currentInst segment hfound hsegment certificates hbindings out called))
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        dsimp only at effect hhost' nextErrors
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        -- Segment bookkeeping consumes no additional quota-counted objects,
        -- signature values, linear-memory bytes, or table elements.
        have nextGrowth : PreparationGrowth store after {} := by
          cases effect <;> exact ⟨hgrowth.limits, hgrowth.objects, hgrowth.signatures, hgrowth.memoryBytes, hgrowth.tableElements⟩
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextErrors, nextStaged, nextObjects, nextGrowth, ?_, ?_, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData⟩, ?_⟩
        · dsimp only at hlength nextStoreSize
          omega
        · intro error rejected
          subst state
          obtain ⟨sameStore, sameHost, cause⟩ := add_element_resource_cause memory hooks floats allocator law
            current platform instIndex index currentInst segment hfound hsegment certificates hbindings error after platform called
          exact ⟨segment, List.getElem_mem hmore, by simpa only [sameStore] using cause.public⟩
        · omega
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, errors, hstaged, hobjects, hgrowth, (by dsimp only [alloc.vec.Vec.length] at hlength hindex ⊢; omega), localCause, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData⟩
  · exact ⟨rfl, True.intro, staged, objectBound, .refl _, (by dsimp; omega), (by intro error impossible; cases impossible), (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl⟩

end Itasca.Store

end

end

end

/-! ## TailCommit -/

section

open Itasca.Representation

/-!
# Tail Commit

Source-sized bounds explain preparation resource refusals before commit. Tail execution and commit connect these explanations to the published instantiation outcome.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std

private theorem PrecommitResourceEvidence.preflight {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {before : runtime.store.Store M} {module : runtime.compiler.ExecutableModule}
    {imports : Slice runtime.Extern} {platform : P} {error}
    (refusal : PreparationPreflight allocator before module error) :
    PrecommitResourceEvidence memory hooks floats allocator before module imports platform error :=
  fun _ _ => Or.inl refusal

private theorem PrecommitResourceEvidence.metadata {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {before : runtime.store.Store M} {module : runtime.compiler.ExecutableModule}
    {imports : Slice runtime.Extern} {platform : P} {error}
    (refusal : PreparationMetadataRefusal allocator before module.module error) :
    PrecommitResourceEvidence memory hooks floats allocator before module imports platform error :=
  fun _ _ => Or.inr (Or.inl refusal)

private theorem PrecommitResourceEvidence.bounded {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {before current : runtime.store.Store M} {module : runtime.compiler.ExecutableModule}
    {imports : Slice runtime.Extern} {platform : P} {error}
    (bounds : PreparationBounds before current module.module)
    (refusal : PreparationResourceRefusal memory allocator current module.module error) :
    PrecommitResourceEvidence memory hooks floats allocator before module imports platform error :=
  fun _ _ => Or.inr (Or.inr ⟨current, bounds, refusal⟩)

private theorem reserve_empty {A T : Type} (allocator : runtime.platform.Alloc A)
    {values : alloc.vec.Vec T} {amount : Usize} (empty : values.val = [])
    (refused : allocator.reserve values amount = .ok (false, values)) :
    allocator.reserve (alloc.vec.Vec.new T) amount = .ok (false, alloc.vec.Vec.new T) := by
  have same : values = alloc.vec.Vec.new T := (alloc.vec.Vec.eq_iff _ _).mpr empty
  simpa only [same] using refused

end Itasca.Store

/-! ## ResourceDecomposition -/

section

/-!
Every actual preparation either returns an ordinary precommit rejection retaining the old store prefix, with its resource evidence, or a staged instance whose item charge yields a fully shaped store. This decomposition imposes no normal-return or termination premise on the computation.

Main declarations: `prepare_instance_resource_decomposition` and `instantiate_inner_resource_decomposition`.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

private theorem deref_len {T : Type} (values : alloc.vec.Vec T) : values.deref.len = values.len := by
  apply UScalar.eq_of_val_eq
  simp [alloc.vec.Vec.deref]

private theorem below_limit (n limit : Usize) (below : ¬n ≥ limit) : n.val < Usize.max := by
  scalar_tac

private theorem below_actual_limit (n limit : Usize) (below : ¬n ≥ limit) : n.val < limit.val := by scalar_tac

private theorem usize_limit (limit : Usize) : limit.val ≤ Usize.max := by scalar_tac

private theorem index_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (Interp.vec_index_given values index value found)
  subst actual
  exact read

private theorem set_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) : values.set index value = values := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  rw [← same]
  exact vec_set_current values index bound

private theorem index_mut_given {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) values index =
      .ok (value, values.set index) := by
  rw [alloc.vec.Vec.index_mut_slice_index]
  unfold alloc.vec.Vec.index_mut_usize
  obtain ⟨actual, read, same⟩ := WP.spec_imp_exists (Interp.vec_index_given values index value found)
  subst actual
  rw [read, bind_tc_ok]

/-- Every actual preparation either returns an ordinary precommit rejection
retaining the old store prefix, with its resource evidence, or a staged
instance whose item charge yields a fully shaped store. Successful preparation
also bounds each quota counter by the starting store plus source demand. The
allocation loops establish the same bounds on early failure, allowing refusal
explanations to omit their execution paths. This decomposition imposes
no normal-return or termination premise on the computation. -/
theorem prepare_instance_resource_decomposition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env)
    (dataValid : ∀ data ∈ module.module.tail.data.val, Itasca.Module.Data.Valid module.module.env data)
    (compiled : Compiler.InitializerMappings module)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (outcome : Result (core.result.Result (runtime.InstanceAddr × Usize) runtime.ExecError × runtime.store.Store M × P))
    (run : runtime.store.instantiate.Store.prepare_instance memory hooks floats allocator before module imports platform = outcome) :
    (∃ error staged, outcome = .ok (.Err error, staged, platform) ∧ StagedPrefix before staged ∧ PrecommitResourceEvidence memory hooks floats allocator before module imports platform error) ∨
    ∃ staged items charged ready inst, staged.instance_items + items = .ok charged ∧
      ready = {staged with instance_items := charged} ∧
      Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      PreparationGrowth before ready (PreparationDemand.source module.module) ∧
      outcome = .ok (.Ok (⟨before.id, before.instances.len⟩, items), staged, platform) := by
  have tableLimits : ∀ ty ∈ module.module.env.table_types.val, LimitsFit ty.limits core.num.U32.MAX := by
    intro ty member
    have canonical := valid.tables ty member
    refine ⟨by simpa [core.num.U32.MAX, U32.rMax] using canonical.1, ?_⟩
    cases maximum : ty.limits.max with
    | none => trivial
    | some high => simpa [maximum, core.num.U32.MAX, U32.rMax] using canonical.2 high (by simp [maximum])
  have memoryLimits : ∀ ty ∈ module.module.env.mem_types.val, LimitsFit ty.limits 65536#u32 := by
    intro ty member
    have canonical := valid.memories ty member
    refine ⟨by simpa using canonical.1, ?_⟩
    cases maximum : ty.limits.max with
    | none => trivial
    | some high => simpa [maximum] using canonical.2 high (by simp [maximum])
  unfold runtime.store.instantiate.Store.prepare_instance at run
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.imports, bind_ok, ] at run
  split at run
  · rename_i mismatch
    exact Or.inl ⟨_, _, run.symm, .refl _, by simp [PrecommitResourceEvidence, PreparationResources]⟩
  · rename_i importCount
    split at run
    · exact Or.inl ⟨_, _, run.symm, .refl _, by
      apply PrecommitResourceEvidence.preflight
      exact Or.inl ⟨rfl,Or.inl (by scalar_tac)⟩⟩
    · rename_i instanceSpace
      simp only [Itasca.metadata.Env.impl.types, Itasca.metadata.Env.impl.func_types, Itasca.metadata.Env.impl.table_types, Itasca.metadata.Env.impl.mem_types, Itasca.metadata.Env.impl.global_types, Itasca.metadata.Env.impl.elements,
        runtime.compiler.ExecutableModule.tail.eq,
        bind_ok, deref_len] at run
      obtain ⟨counted, countsRun, countsErrors, countsPost⟩ := WP.spec_imp_exists
        (item_counts_loop_errors (moduleItemCounts module) 0#usize 0#usize (by simp))
      rcases counted with ⟨items, status⟩
      have countsCause := item_counts_resource_causes (moduleItemCounts module) 0#usize 0#usize (by simp)
      rw [countsRun,WP.spec_ok] at countsCause
      unfold moduleItemCounts at countsRun
      rw [countsRun] at run
      simp only [bind_ok, uncurry_apply_pair] at run
      cases status with
      | Err error =>
        rw [element_items_error] at run
        simp only [bind_ok, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, uncurry_apply_pair] at run
        change Result.ok (.Err error, before, platform) = outcome at run
        exact Or.inl ⟨_, _, run.symm, .refl _, by
          apply PrecommitResourceEvidence.preflight
          dsimp only [ItemSumOutcome] at countsCause
          refine Or.inl ⟨countsCause.1,Or.inr (Or.inl ?_)⟩
          have bound := countsCause.2
          simp [moduleItemCounts,Array.make] at bound
          simp only [moduleItems,alloc.vec.Vec.length]
          omega⟩
      | Ok value =>
        cases value
        obtain ⟨counted, elementRun, itemErrors, elementPost⟩ := WP.spec_imp_exists
          (element_items_loop_errors module items 0#usize (by simp))
        rcases counted with ⟨total, status⟩
        have itemsCause := element_items_resource_causes module items 0#usize (by simp)
        rw [elementRun,WP.spec_ok] at itemsCause
        rw [elementRun] at run
        simp only [bind_ok, uncurry_apply_pair] at run
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
          change Result.ok (.Err error, before, platform) = outcome at run
          exact Or.inl ⟨_, _, run.symm, .refl _, by
            apply PrecommitResourceEvidence.preflight
            dsimp only [ItemSumOutcome] at itemsCause
            refine Or.inl ⟨itemsCause.1,Or.inr (Or.inl ?_)⟩
            have bound := itemsCause.2
            have counts := countsPost rfl
            simpa [moduleItemCounts,moduleItems,counts,Array.make,Nat.add_assoc] using bound⟩
        | Ok value =>
          cases value
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, ] at run
          have exactItems : total.val = moduleItems module := by
            have elements := elementPost rfl
            have counts := countsPost rfl
            simpa [moduleItemCounts, moduleItems, counts, Array.make, Nat.add_assoc] using elements
          obtain ⟨fits, fitsRun, fitsPost⟩ := WP.spec_imp_exists (within_spec before.instance_items total before.limits.max_instance_items)
          rw [fitsRun] at run
          simp only [bind_ok, ] at run
          cases fits with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at run
            exact Or.inl ⟨_, _, run.symm, .refl _, by
              apply PrecommitResourceEvidence.preflight
              exact Or.inl ⟨rfl,Or.inr (Or.inr (by simpa [exactItems] using fitsPost))⟩⟩
          | true =>
            simp only [↓reduceIte] at run
            have itemFits : before.instance_items.val + total.val ≤ before.limits.max_instance_items.val := by
              simpa using fitsPost.symm
            obtain ⟨elementCapacity, dataCapacity, globalLength, elementLength, dataLength⟩ :=
              instance_segment_capacity before module shape accounted total exactItems itemFits
            have importLengths : imports.length = module.module.env.imports.length := by
              change imports.val.length = module.module.env.imports.val.length
              simpa [alloc.vec.Vec.deref] using importCount
            obtain ⟨funcsReserved, funcsRun, funcsCause⟩ := reserve_with_cause allocator law
              (alloc.vec.Vec.new runtime.FuncAddr) module.module.env.func_types.len
            rw [funcsRun] at run
            simp only [bind_ok, uncurry_apply_pair] at run
            cases funcsReserved with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
              change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                outcome at run
              exact Or.inl ⟨_, _, run.symm, .refl _, by exact PrecommitResourceEvidence.preflight (Or.inr ⟨rfl,Or.inl funcsCause⟩)⟩
            | true =>
              simp only [↓reduceIte, bind_ok] at run
              obtain ⟨tablesReserved, tablesRun, tablesCause⟩ := reserve_with_cause allocator law
                (alloc.vec.Vec.new runtime.TableAddr) module.module.env.table_types.len
              rw [tablesRun] at run
              simp only [bind_ok, uncurry_apply_pair] at run
              cases tablesReserved with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                  outcome at run
                exact Or.inl ⟨_, _, run.symm, .refl _, by exact PrecommitResourceEvidence.preflight (Or.inr ⟨rfl,Or.inr (Or.inl tablesCause)⟩)⟩
              | true =>
                simp only [↓reduceIte, bind_ok] at run
                obtain ⟨memoriesReserved, memoriesRun, memoriesCause⟩ := reserve_with_cause allocator law
                  (alloc.vec.Vec.new runtime.MemoryAddr) module.module.env.mem_types.len
                rw [memoriesRun] at run
                simp only [bind_ok, uncurry_apply_pair] at run
                cases memoriesReserved with
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                  change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                    outcome at run
                  exact Or.inl ⟨_, _, run.symm, .refl _, by exact PrecommitResourceEvidence.preflight (Or.inr ⟨rfl,Or.inr (Or.inr (Or.inl memoriesCause))⟩)⟩
                | true =>
                  simp only [↓reduceIte, bind_ok] at run
                  obtain ⟨globalsReserved, globalsRun, globalsCause⟩ := reserve_with_cause allocator law
                    (alloc.vec.Vec.new runtime.GlobalAddr) module.module.env.global_types.len
                  rw [globalsRun] at run
                  simp only [bind_ok, uncurry_apply_pair] at run
                  cases globalsReserved with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                      core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                    change Result.ok (.Err (.Exhausted .Allocation), before, platform) =
                      outcome at run
                    exact Or.inl ⟨_, _, run.symm, .refl _, by exact PrecommitResourceEvidence.preflight (Or.inr ⟨rfl,Or.inr (Or.inr (Or.inr globalsCause))⟩)⟩
                  | true =>
                    simp only [↓reduceIte, bind_ok] at run
                    let seed : runtime.store.ModuleInst := {
                      module := module, types := alloc.vec.Vec.new Usize,
                      funcs := alloc.vec.Vec.new runtime.FuncAddr, tables := alloc.vec.Vec.new runtime.TableAddr,
                      memories := alloc.vec.Vec.new runtime.MemoryAddr, globals := alloc.vec.Vec.new runtime.GlobalAddr,
                      elems := alloc.vec.Vec.new Usize, datas := alloc.vec.Vec.new Usize }
                    have seedMaps : LinkedMaps view before module (module.module.env.imports.val.take 0) seed := by
                      simpa using linked_maps_empty view before seed rfl rfl rfl rfl rfl rfl rfl
                    obtain ⟨⟨linkedStore, linkStatus, inst⟩, linkedRun, sameStore, source, linked⟩ := WP.spec_imp_exists
                      (link_imports_loop memory view laws before shape module imports importLengths handles cache
                        seed 0#usize (by simp) seedMaps)
                    dsimp only at sameStore source linked
                    subst linkedStore
                    rw [linkedRun] at run
                    simp only [bind_ok, uncurry_apply_pair] at run
                    cases linkStatus with
                    | Err error =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                        core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                      exact Or.inl ⟨_, _, run.symm, .refl _, by
                        intro limit rejected
                        have allowed := link_staging_nonresource memory imports before seed 0#usize (.Ok ()) True.intro linkedRun
                        subst error
                        simp [ErrorAllowed,LinkFailure] at allowed⟩
                    | Ok value =>
                      cases value
                      have maps : LinkedMaps view before inst.module inst.module.module.env.imports.val inst := by
                        simpa only [source] using linked rfl
                      have instCache : Cache inst.module.module.env tables memories := by simpa only [source] using cache
                      simp only [bind_ok] at run
                      obtain ⟨typesReserved, typesRun, typesCause⟩ := reserve_with_cause allocator law inst.types inst.module.module.env.types.len
                      rw [typesRun] at run
                      simp only [bind_ok, uncurry_apply_pair] at run
                      cases typesReserved with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte,
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                          core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                        exact Or.inl ⟨_, _, run.symm, .refl _, by
                          apply PrecommitResourceEvidence.metadata
                          refine ⟨rfl, Or.inl ?_⟩
                          simpa only [source] using (reserve_empty allocator maps.types typesCause)⟩
                      | true =>
                        simp only [↓reduceIte, bind_ok] at run
                        have eta : {inst with types := inst.types} = inst := by cases inst; rfl
                        rw [eta] at run
                        have objectBound : objectCount before ≤ Usize.max := by
                          have bound := shape.objectLimit
                          unfold objectCount
                          scalar_tac
                        have emptyTypes : TypeEntries before (inst.module.module.env.types.val.take 0) inst.types.val := by
                          simp [TypeEntries, maps.types]
                        obtain ⟨out, typedRun, typed, typeInst, status, parts, typeStore, typeMap, typePrefix, typeBound, typeEntries, typeGrowth, typeRefusal⟩ :=
                          WP.spec_imp_exists (type_staging_resource_loop memory allocator law before before inst inst 0#usize
                            (by simp) rfl rfl (.refl _) objectBound emptyTypes (by simpa [PreparationDemand.types] using PreparationGrowth.refl before))
                        subst out
                        have typedTotal := typeGrowth
                        have typedBudget : PreparationBounds before typed module.module := by
                          refine ⟨?_, ?_, ?_⟩
                          · apply typedTotal.mono <;>
                              dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                              (try simp only [source]) <;> omega
                          · have same := congrArg runtime.store.Store.elems typeStore; dsimp only at same; rw [same]; omega
                          · have same := congrArg runtime.store.Store.datas typeStore; dsimp only at same; rw [same]; omega
                        rw [typedRun] at run
                        simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                        cases status with
                        | Err error =>
                          simp only [
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                            core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                          exact Or.inl ⟨_, _, run.symm, typePrefix, by
                            apply PrecommitResourceEvidence.bounded typedBudget
                            refine Or.inl ?_
                            simpa only [source] using (typeRefusal error rfl)⟩
                        | Ok value =>
                          cases value
                          simp only [bind_ok] at run
                          have typeStore_funcs := congrArg runtime.store.Store.funcs typeStore
                          dsimp only at typeStore_funcs
                          have typeStore_tables := congrArg runtime.store.Store.tables typeStore
                          dsimp only at typeStore_tables
                          have typeStore_memories := congrArg runtime.store.Store.memories typeStore
                          dsimp only at typeStore_memories
                          have typeStore_globals := congrArg runtime.store.Store.globals typeStore
                          dsimp only at typeStore_globals
                          have typeStore_instances := congrArg runtime.store.Store.instances typeStore
                          dsimp only at typeStore_instances
                          have typeStore_elems := congrArg runtime.store.Store.elems typeStore
                          dsimp only at typeStore_elems
                          have typeStore_datas := congrArg runtime.store.Store.datas typeStore
                          dsimp only at typeStore_datas
                          have typeMap_module := congrArg runtime.store.ModuleInst.module typeMap
                          dsimp only at typeMap_module
                          have typeMap_tables := congrArg runtime.store.ModuleInst.tables typeMap
                          dsimp only at typeMap_tables
                          have typeMap_memories := congrArg runtime.store.ModuleInst.memories typeMap
                          dsimp only at typeMap_memories
                          have typeMap_globals := congrArg runtime.store.ModuleInst.globals typeMap
                          dsimp only at typeMap_globals
                          have typeMap_elements := congrArg runtime.store.ModuleInst.elems typeMap
                          dsimp only at typeMap_elements
                          have typeMap_data := congrArg runtime.store.ModuleInst.datas typeMap
                          dsimp only at typeMap_data
                          have typeSource : typeInst.module = inst.module := by
                            have h := congrArg runtime.store.ModuleInst.module typeMap
                            exact h
                          have typeFuncs : typeInst.funcs = inst.funcs := by
                            have h := congrArg runtime.store.ModuleInst.funcs typeMap
                            exact h
                          have typesComplete : typeInst.types.length = inst.module.module.env.types.length :=
                            (typeEntries rfl).length_eq.symm
                          have sourceIndices := cache_defined_type_bounds instCache typeInst.types typesComplete
                          have preparedIndices : ∀ idx ∈ typeInst.module.module.env.func_type_indices.val,
                              idx.val < typeInst.types.length := by simpa only [typeSource] using sourceIndices
                          have importedIssued := (maps.bindings shape).funcs
                          have typedIssued : ∀ addr ∈ typeInst.funcs.val, addr.index.val < typed.funcs.length := by
                            simpa only [typeFuncs, typeStore_funcs] using importedIssued
                          have functionCapacity : typeInst.funcs.length + typeInst.module.module.env.func_type_indices.val.length ≤ Usize.max := by
                            simpa only [typeFuncs, typeSource] using maps.function_capacity instCache
                          have functionChecked := function_staging_resource_loop memory allocator law typed typed typeInst typeInst before.instances.len 0#usize
                            (by simp) rfl rfl (.refl _) typeBound preparedIndices typedIssued (by simp) functionCapacity (.refl _)
                          obtain ⟨out, functionRun, functions, funcInst, status, parts, functionStore, functionMap,
                              functionPrefix, functionBound, functionIssued, functionCount, functionGrowth, functionRefusal⟩ := WP.spec_imp_exists functionChecked
                          subst out
                          have functionTotal := typedTotal.trans functionGrowth
                          have functionBudget : PreparationBounds before functions module.module := by
                            refine ⟨?_, ?_, ?_⟩
                            · apply functionTotal.mono <;>
                                dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                  PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                (try simp only [typeSource, source]) <;> omega
                            · have same := congrArg runtime.store.Store.elems functionStore; dsimp only at same; rw [same]; exact typedBudget.elements
                            · have same := congrArg runtime.store.Store.datas functionStore; dsimp only at same; rw [same]; exact typedBudget.datas
                          rw [functionRun] at run
                          simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                          cases status with
                          | Err error =>
                            simp only [
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                              core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                            exact Or.inl ⟨_, _, run.symm, typePrefix.trans functionPrefix, by
                              apply PrecommitResourceEvidence.bounded functionBudget
                              refine Or.inr (Or.inl ?_)
                              simpa only [typeSource, source] using (functionRefusal error rfl)⟩
                          | Ok value =>
                            cases value
                            simp only [bind_ok] at run
                            have functionStore_tables := congrArg runtime.store.Store.tables functionStore
                            dsimp only at functionStore_tables
                            have functionStore_memories := congrArg runtime.store.Store.memories functionStore
                            dsimp only at functionStore_memories
                            have functionStore_globals := congrArg runtime.store.Store.globals functionStore
                            dsimp only at functionStore_globals
                            have functionStore_instances := congrArg runtime.store.Store.instances functionStore
                            dsimp only at functionStore_instances
                            have functionStore_elems := congrArg runtime.store.Store.elems functionStore
                            dsimp only at functionStore_elems
                            have functionStore_datas := congrArg runtime.store.Store.datas functionStore
                            dsimp only at functionStore_datas
                            have functionMap_module := congrArg runtime.store.ModuleInst.module functionMap
                            dsimp only at functionMap_module
                            have functionMap_tables := congrArg runtime.store.ModuleInst.tables functionMap
                            dsimp only at functionMap_tables
                            have functionMap_memories := congrArg runtime.store.ModuleInst.memories functionMap
                            dsimp only at functionMap_memories
                            have functionMap_globals := congrArg runtime.store.ModuleInst.globals functionMap
                            dsimp only at functionMap_globals
                            have functionMap_elements := congrArg runtime.store.ModuleInst.elems functionMap
                            dsimp only at functionMap_elements
                            have functionMap_data := congrArg runtime.store.ModuleInst.datas functionMap
                            dsimp only at functionMap_data
                            have functionSource : funcInst.module = inst.module := by
                              simpa only [functionMap_module] using typeSource
                            obtain ⟨tableStart, importedTables⟩ := maps.table_start instCache
                            have tableStartBound : funcInst.tables.len.val ≤ funcInst.module.module.env.table_types.val.length := by
                              simpa only [alloc.vec.Vec.len_val, functionMap_tables, typeMap_tables, functionMap_module, typeMap_module] using tableStart
                            have tableIssued : ∀ addr ∈ funcInst.tables.val, addr.index.val < functions.tables.length := by
                              simpa only [functionMap_tables, typeMap_tables, functionStore_tables, typeStore_tables] using importedTables
                            have tableChecked := table_staging_resource_loop memory allocator law functions functions funcInst funcInst funcInst.tables.len
                              tableStartBound rfl rfl (.refl _) functionBound tableIssued (by simp)
                                (by constructor <;> dsimp [PreparationDemand.tables] <;> omega)
                            obtain ⟨out, tableRun, tabled, tableInst, status, parts, tableStore, tableMap, tablePrefix, tableBound, tableAddresses, tableCount, tableGrowth, tableRefusal⟩ := WP.spec_imp_exists tableChecked
                            subst out
                            have tableTotal := functionTotal.trans tableGrowth
                            have tableBudget : PreparationBounds before tabled module.module := by
                              refine ⟨?_, ?_, ?_⟩
                              · apply tableTotal.mono <;>
                                  dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                    PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                  (try simp only [functionSource, typeSource, source]) <;> omega
                              · have same := congrArg runtime.store.Store.elems tableStore; dsimp only at same; rw [same]; exact functionBudget.elements
                              · have same := congrArg runtime.store.Store.datas tableStore; dsimp only at same; rw [same]; exact functionBudget.datas
                            rw [tableRun] at run
                            simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                            cases status with
                            | Err error =>
                              simp only [
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                              exact Or.inl ⟨_, _, run.symm, typePrefix.trans (functionPrefix.trans tablePrefix), by
                                intro limit rejected
                                subst error
                                refine Or.inr (Or.inr ⟨tabled, tableBudget, Or.inr (Or.inr (Or.inl ⟨limit, rfl, ?_⟩))⟩)
                                simpa only [functionSource, source] using (tableRefusal limit rfl)⟩
                            | Ok value =>
                              cases value
                              simp only [bind_ok] at run
                              have tableStore_funcs := congrArg runtime.store.Store.funcs tableStore
                              dsimp only at tableStore_funcs
                              have tableStore_memories := congrArg runtime.store.Store.memories tableStore
                              dsimp only at tableStore_memories
                              have tableStore_globals := congrArg runtime.store.Store.globals tableStore
                              dsimp only at tableStore_globals
                              have tableStore_instances := congrArg runtime.store.Store.instances tableStore
                              dsimp only at tableStore_instances
                              have tableStore_elems := congrArg runtime.store.Store.elems tableStore
                              dsimp only at tableStore_elems
                              have tableStore_datas := congrArg runtime.store.Store.datas tableStore
                              dsimp only at tableStore_datas
                              have tableMap_module := congrArg runtime.store.ModuleInst.module tableMap
                              dsimp only at tableMap_module
                              have tableMap_funcs := congrArg runtime.store.ModuleInst.funcs tableMap
                              dsimp only at tableMap_funcs
                              have tableMap_memories := congrArg runtime.store.ModuleInst.memories tableMap
                              dsimp only at tableMap_memories
                              have tableMap_globals := congrArg runtime.store.ModuleInst.globals tableMap
                              dsimp only at tableMap_globals
                              have tableMap_elements := congrArg runtime.store.ModuleInst.elems tableMap
                              dsimp only at tableMap_elements
                              have tableMap_data := congrArg runtime.store.ModuleInst.datas tableMap
                              dsimp only at tableMap_data
                              obtain ⟨memoryStart, importedMemories⟩ := maps.memory_start instCache
                              have memoryStartBound : tableInst.memories.len.val ≤ tableInst.module.module.env.mem_types.val.length := by
                                simpa only [alloc.vec.Vec.len_val, tableMap_memories, functionMap_memories, typeMap_memories, tableMap_module, functionMap_module, typeMap_module] using memoryStart
                              have memoryIssued : ∀ addr ∈ tableInst.memories.val, addr.index.val < tabled.memories.length := by
                                simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableStore_memories, functionStore_memories, typeStore_memories] using importedMemories
                              have memoryChecked := memory_staging_resource_loop memory allocator law view laws tabled tabled tableInst tableInst tableInst.memories.len
                                memoryStartBound rfl rfl (.refl _) tableBound memoryIssued (by simp)
                                (by constructor <;> dsimp [PreparationDemand.memories] <;> omega)
                              obtain ⟨out, memoryRun, prepared, preparedInst, status, parts, memoryStore, memoryMap, memoryPrefix, memoryBound, memoryAddresses, memoryCount, memoryGrowth, memoryRefusal⟩ := WP.spec_imp_exists memoryChecked
                              subst out
                              have memoryTotal := tableTotal.trans memoryGrowth
                              have preparedBudget : PreparationBounds before prepared module.module := by
                                refine ⟨?_, ?_, ?_⟩
                                · apply memoryTotal.mono <;>
                                    dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                      PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                    (try simp only [tableMap_module, functionSource, typeSource, source]) <;> omega
                                · have same := congrArg runtime.store.Store.elems memoryStore; dsimp only at same; rw [same]; exact tableBudget.elements
                                · have same := congrArg runtime.store.Store.datas memoryStore; dsimp only at same; rw [same]; exact tableBudget.datas
                              rw [memoryRun] at run
                              simp only [typeParts, bind_ok, uncurry_apply_pair] at run
                              cases status with
                              | Err error =>
                                simp only [
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                  core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                exact Or.inl ⟨_, _, run.symm, typePrefix.trans (functionPrefix.trans (tablePrefix.trans memoryPrefix)), by
                                  intro limit rejected
                                  subst error
                                  refine Or.inr (Or.inr ⟨prepared, preparedBudget, Or.inr (Or.inr (Or.inr (Or.inl ⟨limit, rfl, ?_⟩)))⟩)
                                  simpa only [tableMap_module, functionSource, source] using (memoryRefusal limit rfl)⟩
                              | Ok value =>
                                cases value
                                have preparedFacts := preparation_success memory allocator law view laws before inst shape maps instCache
                                  before.instances.len typed functions tabled prepared typeInst funcInst tableInst preparedInst
                                  typedRun functionRun tableRun memoryRun
                                obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
                                  preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
                                  preparedBindings, preparedImports, preparedSegments⟩ := preparedFacts
                                simp only [bind_ok] at run
                                obtain ⟨instancesReserved, instancesRun, instancesCause⟩ := reserve_with_cause allocator law prepared.instances 1#usize
                                rw [instancesRun] at run
                                simp only [bind_ok, uncurry_apply_pair] at run
                                cases instancesReserved with
                                | false =>
                                  simp only [Bool.false_eq_true, ↓reduceIte,
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                    core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                  exact Or.inl ⟨_, _, run.symm, preparedPrefix, by
                                    apply PrecommitResourceEvidence.metadata
                                    refine ⟨rfl, Or.inr (Or.inr (Or.inr (?_)))⟩
                                    simpa only [preparedInstances] using (instancesCause)⟩
                                | true =>
                                  simp only [↓reduceIte, bind_ok] at run
                                  have instanceRoom : prepared.instances.length < Usize.max := by
                                    rw [preparedInstances]
                                    exact below_limit before.instances.len before.limits.max_instances instanceSpace
                                  have preparedAccounting : SegmentAccounting prepared := by
                                    constructor
                                    · simpa only [preparedElements, preparedInstances] using accounted.elements
                                    · simpa only [preparedData, preparedInstances] using accounted.datas
                                  have emptyElements : preparedInst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
                                  have emptyData : preparedInst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
                                  obtain ⟨publishedInstances, publishedRun, appended, publishedFound, publishedPrefix,
                                    publishedBindings, publishedImports, publishedSegments, publishedAccounting, publishedObjects⟩ :=
                                    WP.spec_imp_exists (publish_prepared_instance prepared preparedInst instanceRoom preparedBindings
                                      preparedImports preparedSegments preparedAccounting emptyElements emptyData)
                                  rw [publishedRun] at run
                                  simp only [bind_ok] at run
                                  let published := {prepared with instances := publishedInstances}
                                  have publicationGrowth : PreparationGrowth prepared published {} := by
                                    constructor <;> dsimp [published] <;> omega
                                  have publishedTotal := memoryTotal.trans publicationGrowth
                                  have publishedBudget : PreparationBounds before published module.module := by
                                    refine ⟨?_, ?_, ?_⟩
                                    · apply publishedTotal.mono <;>
                                        dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                          PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                        (try simp only [tableMap_module, functionSource, typeSource, source]) <;> omega
                                    · exact preparedBudget.elements
                                    · exact preparedBudget.datas
                                  have indexFound : published.instances.val[before.instances.len.val]? = some preparedInst := by
                                    simpa only [preparedInstances] using publishedFound
                                  have publishedBound : objectCount published ≤ Usize.max := by
                                    change objectCount {prepared with instances := publishedInstances} ≤ Usize.max
                                    rw [publishedObjects]
                                    exact preparedBound
                                  have globalValid : ∀ global ∈ preparedInst.module.module.env.globals.val,
                                      Itasca.Module.Constants.Valid preparedInst.module.module.env global.init global.gtype.valtype := by
                                    simpa only [preparedSource, source] using valid.globals
                                  have globalCapacity : preparedInst.globals.length + (preparedInst.module.module.env.globals.val.length - 0) ≤ Usize.max := by
                                    simpa only [preparedGlobalMap, preparedSource, Nat.sub_zero] using maps.global_capacity instCache
                                  have publishedCompiled : Compiler.InitializerMappings preparedInst.module := by simpa only [preparedSource, source] using compiled
                                  obtain ⟨out, globalRun, globalStore, globalStatus, parts, globalErrors, globalPrefix, globalBound, globalGrowth, globalRefusal,
                                    globalAccounting, globalMetadata, globalInst, globalFound, globalSource, globalBindings, globalImports,
                                    globalSegments, globalElements, globalData, globalElementMap, globalDataMap⟩ := WP.spec_imp_exists
                                    (global_staging_resource_loop memory hooks floats allocator law before published platform before.instances.len 0#usize
                                      preparedInst (preparedPrefix.trans publishedPrefix) (by simp) indexFound publishedCompiled
                                      globalValid publishedBindings publishedImports publishedSegments publishedBound (by simp) globalCapacity)
                                  subst out
                                  have globalTotal := publishedTotal.trans globalGrowth
                                  have globalBudget : PreparationBounds before globalStore module.module := by
                                    refine ⟨?_, ?_, ?_⟩
                                    · apply globalTotal.mono <;>
                                        dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                          PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                        (try simp only [preparedSource, tableMap_module, functionSource, typeSource, source]) <;> omega
                                    · simpa only [globalElements] using publishedBudget.elements
                                    · simpa only [globalData] using publishedBudget.datas
                                  rw [globalRun] at run
                                  simp only [storeParts, bind_ok, uncurry_apply_pair] at run
                                  cases globalStatus with
                                  | Err error =>
                                    simp only [
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                      core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                    exact Or.inl ⟨_, _, run.symm, globalPrefix, by
                                      apply PrecommitResourceEvidence.bounded globalBudget
                                      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
                                      simpa only [preparedSource, source] using (globalRefusal error rfl)⟩
                                  | Ok value =>
                                    cases value
                                    simp only [bind_ok] at run
                                    rw [index_given globalStore.instances before.instances.len globalInst globalFound, bind_ok] at run
                                    rw [index_mut_given globalStore.instances before.instances.len globalInst globalFound, bind_ok] at run
                                    simp only [uncurry_apply_pair] at run
                                    obtain ⟨elementsReserved, elementsRun, elementsCause⟩ := reserve_with_cause allocator law globalInst.elems globalInst.module.module.env.elements.len
                                    rw [elementsRun] at run
                                    simp only [bind_ok, uncurry_apply_pair] at run
                                    have elementEta : {globalInst with elems := globalInst.elems} = globalInst := by cases globalInst; rfl
                                    simp only [set_given globalStore.instances before.instances.len globalInst globalFound] at run
                                    cases elementsReserved with
                                    | false =>
                                      simp only [Bool.false_eq_true, ↓reduceIte,
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                        core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                      exact Or.inl ⟨_, _, run.symm, globalPrefix, by
                                        apply PrecommitResourceEvidence.metadata
                                        refine ⟨rfl, Or.inr (Or.inl ?_)⟩
                                        simpa only [globalSource, preparedSource, source] using (reserve_empty allocator (by rw [globalElementMap]; exact emptyElements) elementsCause)⟩
                                    | true =>
                                      simp only [↓reduceIte, bind_ok] at run
                                      have globalCompiled : Compiler.InitializerMappings globalInst.module := by
                                        simpa only [globalSource] using publishedCompiled
                                      have elementValid : ∀ segment ∈ globalInst.module.module.env.elements.val,
                                          Itasca.Module.Segments.elementValid globalInst.module.module.env segment := by
                                        simpa only [globalSource, preparedSource, source] using valid.elements
                                      have elementStoreCapacity : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
                                        simpa only [globalElements, published, preparedElements, globalSource, preparedSource, source, Nat.sub_zero] using elementCapacity
                                      have elementMapCapacity : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
                                        have empty : globalInst.elems.val = [] := by rw [globalElementMap]; exact emptyElements
                                        simpa only [alloc.vec.Vec.length, empty, List.length_nil, Nat.zero_add, globalSource,
                                          preparedSource, source, Nat.sub_zero] using elementLength
                                      obtain ⟨out, elementStageRun, elementStore, elementStatus, parts, elementErrors, elementPrefix, elementBound, elementGrowth, elementLengthBound, elementRefusal,
                                        elementAccounting, elementMetadata, elementInst, elementFound, elementSource, elementBindings, elementImports,
                                        elementSegments, elementData, elementDataMap⟩ := WP.spec_imp_exists
                                        (element_staging_resource_loop memory hooks floats allocator law before globalStore platform before.instances.len 0#usize
                                          globalInst globalPrefix (by simp) globalFound globalCompiled elementValid globalBindings globalImports
                                          globalSegments globalBound (by simp) elementStoreCapacity elementMapCapacity)
                                      subst out
                                      have elementTotal := globalTotal.trans elementGrowth
                                      have elementBudget : PreparationBounds before elementStore module.module := by
                                        refine ⟨?_, ?_, ?_⟩
                                        · apply elementTotal.mono <;>
                                            dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                              PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                            (try simp only [preparedSource, tableMap_module, functionSource, typeSource, source]) <;> omega
                                        · simpa only [globalElements, published, preparedElements, globalSource, preparedSource, source] using elementLengthBound
                                        · simpa only [elementData] using globalBudget.datas
                                      rw [elementStageRun] at run
                                      simp only [storeParts, bind_ok, uncurry_apply_pair] at run
                                      cases elementStatus with
                                      | Err error =>
                                        simp only [
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                          core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                        exact Or.inl ⟨_, _, run.symm, elementPrefix, by
                                          apply PrecommitResourceEvidence.bounded elementBudget
                                          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
                                          simpa only [globalSource, preparedSource, source] using (elementRefusal error rfl)⟩
                                      | Ok value =>
                                        cases value
                                        simp only [bind_ok] at run
                                        rw [index_given elementStore.instances before.instances.len elementInst elementFound, bind_ok] at run
                                        rw [index_mut_given elementStore.instances before.instances.len elementInst elementFound, bind_ok] at run
                                        simp only [uncurry_apply_pair] at run
                                        obtain ⟨dataReserved, dataRun, dataCause⟩ := reserve_with_cause allocator law elementInst.datas elementInst.module.module.tail.data.len
                                        rw [dataRun] at run
                                        simp only [bind_ok, uncurry_apply_pair] at run
                                        have dataEta : {elementInst with datas := elementInst.datas} = elementInst := by cases elementInst; rfl
                                        simp only [set_given elementStore.instances before.instances.len elementInst elementFound] at run
                                        cases dataReserved with
                                        | false =>
                                          simp only [Bool.false_eq_true, ↓reduceIte,
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                            core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                          exact Or.inl ⟨_, _, run.symm, elementPrefix, by
                                            apply PrecommitResourceEvidence.metadata
                                            refine ⟨rfl, Or.inr (Or.inr (Or.inl ?_))⟩
                                            simpa only [elementSource, globalSource, preparedSource, source] using (reserve_empty allocator (by rw [elementDataMap, globalDataMap]; exact emptyData) dataCause)⟩
                                        | true =>
                                          simp only [↓reduceIte, bind_ok] at run
                                          have dataStoreCapacity : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
                                            simpa only [elementData, globalData, published, preparedData, elementSource, globalSource,
                                              preparedSource, source, Nat.sub_zero] using dataCapacity
                                          have dataMapCapacity : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
                                            have empty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap]; exact emptyData
                                            simpa only [alloc.vec.Vec.length, empty, List.length_nil, Nat.zero_add, elementSource, globalSource,
                                              preparedSource, source, Nat.sub_zero] using dataLength
                                          obtain ⟨out, dataStageRun, dataStore, dataStatus, parts, dataPrefix, dataBound, dataGrowth, dataElements, dataLengthBound, dataRefusal, dataAccounting, dataMetadata,
                                            dataInst, dataFound, dataSource, dataBindings, dataImports, dataSegments⟩ := WP.spec_imp_exists
                                            (data_staging_resource_loop memory allocator law before elementStore before.instances.len 0#usize elementInst
                                              elementPrefix (by simp) elementFound elementBindings elementImports elementSegments elementBound
                                              (by simp) dataStoreCapacity dataMapCapacity)
                                          subst out
                                          have dataTotal := elementTotal.trans dataGrowth
                                          have dataBudget : PreparationBounds before dataStore module.module := by
                                            refine ⟨?_, ?_, ?_⟩
                                            · apply dataTotal.mono <;>
                                                dsimp [PreparationDemand.source, PreparationDemand.types, PreparationDemand.tables,
                                                  PreparationDemand.memories, PreparationDemand.add, alloc.vec.Vec.length] <;>
                                                (try simp only [preparedSource, tableMap_module, functionSource, typeSource, source]) <;> omega
                                            · simpa only [dataElements] using elementBudget.elements
                                            · simpa only [elementData, globalData, published, preparedData, elementSource, globalSource, preparedSource, source] using dataLengthBound
                                          rw [dataStageRun] at run
                                          simp only [storeStateParts, bind_ok, uncurry_apply_pair] at run
                                          cases dataStatus with
                                          | Err error =>
                                            simp only [
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                              core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
                                            exact Or.inl ⟨_, _, run.symm, dataPrefix, by
                                              apply PrecommitResourceEvidence.bounded dataBudget
                                              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))
                                              simpa only [elementSource, globalSource, preparedSource, source] using (dataRefusal error rfl)⟩
                                          | Ok value =>
                                            cases value
                                            simp only [bind_ok] at run
                                            have chargeBound : dataStore.instance_items.val + total.val ≤ Usize.max := by
                                              rw [dataPrefix.instanceItems]
                                              exact itemFits.trans (usize_limit _)
                                            obtain ⟨charged, chargeRun, chargeSpec⟩ := WP.spec_imp_exists
                                              (Usize.add_spec (x := dataStore.instance_items) (y := total) chargeBound)
                                            have counted : charged.val = before.instance_items.val + moduleItems inst.module := by
                                              simpa only [dataPrefix.instanceItems, exactItems, source] using chargeSpec
                                            have limited : charged.val ≤ before.limits.max_instance_items.val := by
                                              rw [chargeSpec, dataPrefix.instanceItems]
                                              exact itemFits
                                            have actualRoom : before.instances.length < before.limits.max_instances.val := by
                                              simpa only [alloc.vec.Vec.len_val] using below_actual_limit _ _ instanceSpace
                                            obtain ⟨next, nextFound, nextSource, readyShape, typeBindings, retained, segmentsAccounted, readyCode⟩ :=
                                              prepared_commit_shape memory hooks floats allocator law view laws before inst platform shape accounted maps instCache
                                                (by simpa only [source] using valid) (by simpa only [source] using compiled) actualRoom
                                                (by simpa only [source] using elementCapacity) (by simpa only [source] using dataCapacity)
                                                charged counted limited typed functions tabled prepared typeInst funcInst tableInst preparedInst
                                                typedRun functionRun tableRun memoryRun publishedInstances publishedRun
                                                globalStore elementStore dataStore globalRun elementStageRun dataStageRun
                                            let ready := {dataStore with instance_items := charged}
                                            refine Or.inr ⟨dataStore, total, charged, ready, next, chargeRun, rfl, readyShape, nextFound, nextSource.trans source, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                                            · have same : next = dataInst := Option.some.inj (nextFound.symm.trans dataFound)
                                              subst next
                                              exact ⟨dataImports.funcs, dataImports.globals⟩
                                            · exact ⟨typeBindings.tables, typeBindings.elements⟩
                                            · exact ⟨segmentsAccounted.elements, segmentsAccounted.datas⟩
                                            · exact readyCode
                                            · exact ⟨{
                                                seed := inst, source := source, maps := maps, instanceRoom := actualRoom,
                                                importsLength := importLengths, linkRun := linkedRun,
                                                elementCapacity := by simpa only [source] using elementCapacity,
                                                dataCapacity := by simpa only [source] using dataCapacity,
                                                typed := typed, functions := functions, tabled := tabled, prepared := prepared,
                                                typeInst := typeInst, funcInst := funcInst, tableInst := tableInst, inst := preparedInst,
                                                typeRun := typedRun, functionRun := functionRun, tableRun := tableRun, memoryRun := memoryRun,
                                                publishedInstances := publishedInstances, publicationRun := publishedRun,
                                                globalStore := globalStore, elementStore := elementStore, dataStore := dataStore,
                                                globalRun := globalRun, elementRun := elementStageRun, dataRun := dataStageRun,
                                                charged := charged, counted := counted, limited := limited, committed := rfl }⟩
                                            · exact ⟨dataBudget.growth.limits, dataBudget.growth.objects,
                                                dataBudget.growth.signatures, dataBudget.growth.memoryBytes,
                                                dataBudget.growth.tableElements⟩
                                            · exact run.symm

/-- Every actual instantiation computation either returns an ordinary precommit
rejection retaining the old store prefix, or reaches a fully shaped committed
store and executes exactly the segment/start tail. This decomposition imposes
no normal-return or termination premise on the computation. -/
theorem instantiate_inner_resource_decomposition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env)
    (dataValid : ∀ data ∈ module.module.tail.data.val, Itasca.Module.Data.Valid module.module.env data)
    (compiled : Compiler.InitializerMappings module)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (outcome : Result (core.result.Result runtime.Instantiated runtime.ExecError × runtime.store.Store M × P × Bool))
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false = outcome) :
    (∃ error staged, outcome = .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged ∧ PrecommitResourceEvidence memory hooks floats allocator before module imports platform error) ∨
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
        outcome := by
  unfold runtime.store.instantiate.Store.instantiate_inner at run
  rcases prepare_instance_resource_decomposition memory hooks floats allocator law view laws before module
      imports platform shape accounted cache valid dataValid compiled handles _ rfl with
    ⟨error, staged, prepared, rest⟩ | ⟨staged, items, charged, ready, inst, charge, rfl, rest⟩
  · rw [prepared] at run
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, uncurry_apply_pair] at run
    exact Or.inl ⟨error, staged, run.symm, rest⟩
  · obtain ⟨shaped, found, source, imported, types, accounting, code, linked, _growth, prepared⟩ := rest
    rw [prepared] at run
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, charge] at run
    exact Or.inr ⟨_, inst, shaped, found, source, imported, types, accounting, code, linked, run⟩

end Itasca.Store

end

/-! ## TailCommitExecution -/

section

/-!
Every normal result of the remaining initializer computation carries the committed flag.

Main declarations: `instantiate_tail_committed`.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Every normal result of the remaining initializer computation carries
the committed flag. -/
theorem instantiate_tail_committed {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (result : core.result.Result runtime.Instantiated runtime.ExecError)
    (after : runtime.store.Store M) (host : P) (committed : Bool)
    (run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
      .ok (result, after, host, committed)) : committed = true := by
  unfold runtime.store.instantiate.Store.commit_instance at run
  obtain ⟨⟨status, state, context⟩, initRun, run⟩ := normal_bind_exists _ _ _ run
  simp only [uncurry_apply_pair] at run
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
    exact (congrArg (fun out => out.2.2.2) (Result.ok_injective run)).symm
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨inst, instRun, run⟩ := normal_bind_exists _ _ _ run
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.start, bind_ok] at run
    split at run
    · exact (congrArg (fun out => out.2.2.2) (Result.ok_injective run)).symm
    · obtain ⟨index, indexRun, run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨address, addressRun, run⟩ := normal_bind_exists _ _ _ run
      exact (congrArg (fun out => out.2.2.2) (Result.ok_injective run)).symm

end Itasca.Store

end

/-! ## TailCommit -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Tuple-form consequence of the canonical committed-tail theorem. -/
theorem instantiate_tail_committed_result {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (out : core.result.Result runtime.Instantiated runtime.ExecError × runtime.store.Store M × P × Bool)
    (run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false = .ok out) :
    out.2.2.2 = true := by
  exact instantiate_tail_committed memory hooks floats allocator identity store platform
    out.1 out.2.1 out.2.2.1 out.2.2.2 run

end Itasca.Store

end

end
