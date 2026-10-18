import Exec.Store.Preparation.StagingTypeCertificates
import Exec.Store.Invariant.AllocatedGlobalLoop
import Exec.Store.Invariant.AllocatedElementLoop
import Exec.Store.Invariant.AllocatedDataLoop

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Successful actual global, element, and data staging constructs the source/raw
segment type bindings and preserves every issued element reference. The initial
empty segment maps come from publication of the newly prepared instance. -/
theorem staging_allocated_certificates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.Instance)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Code.InitializerMappings inst.module)
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elements.val = []) (emptyData : inst.data.val = [])
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (allocated : AllocationShape view store)
    (globalIssued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.instantiate_inner_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.instantiate_inner_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.instantiate_inner_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      SegmentTypeBindings after next ∧ ElementContents after ∧ GlobalContents after ∧
      next.globals.length = inst.globals.length + inst.module.module.env.globals.val.length ∧
      next.elements.length = inst.module.module.env.elements.val.length ∧
      next.data.length = inst.module.module.tail.data.val.length ∧
      (∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length) ∧
      (∀ address ∈ next.data.val, address.val < after.datas.length) ∧
      InitializerFunctionMetadata store inst after next ∧
      ElementTypeMap after next.module.module.env.elements.val next.elements.val ∧ AllocationShape view after ∧
      StagedPrefix before after ∧ (SegmentAccounting store → SegmentAccounting after) := by
  have contents : ElementContents store := allocated.elements
  have globals := global_allocated_loop memory hooks floats allocator law view before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound allocated (by simp) (by simpa using globalCapacity) globalIssued
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalAllocated, globalsCanonical, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, nextGlobalIssued, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap, globalCount⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp result
  have globalTables := (globalMetadata.resolve globalFound).table_types tables
  have globalContents : ElementContents globalStore := by
    have funcs := (globalMetadata.resolve globalFound).functions
    have externs := globalStaged.externs.trans staged.externs.symm
    simpa only [ElementContents, ReferenceShape, globalElements, funcs, externs] using contents
  have globalEmpty : globalInst.elements.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elements.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elements.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements  := element_allocated_loop memory hooks floats allocator law view before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound globalAllocated
    (by simp) elementRoom mapRoom (fun _ => initialTypes) globalContents
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementAllocated, elementContents, elementGlobals, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementGlobalMap, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp result
  have elementTables := (elementMetadata.resolve elementFound).table_types globalTables
  have elementEmpty : elementInst.data.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.data.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data  := data_allocated_loop memory allocator law view before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound elementAllocated
    (by simp) dataRoom dataMapRoom (by simpa only [elementSource] using elementTypes rfl) elementContents (by simp [elementEmpty])
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalAllocated, finalContents, finalGlobals, finalAccounted, finalMetadata,
    next, nextFound, nextSource, nextDataIssued, nextGlobalMap, nextBindings, nextImports, nextSegments, nextTypes, finalCount⟩ := data
  obtain ⟨rfl, rfl⟩ := (storeStateParts_inj _ _ _ _).mp result
  have finalTables := (finalMetadata.resolve nextFound).table_types elementTables
  refine ⟨next, nextFound, nextSource.trans (elementSource.trans globalSource), ?_, finalContents, ?_, ?_, ?_, ?_, ?_, nextDataIssued, ?_, ?_, finalAllocated, finalStaged, fun h => finalAccounted (elementAccounted (globalAccounted h))⟩
  · apply segment_type_bindings_of_maps
    · simpa only [nextSource, elementSource, globalSource] using finalTables
    · simpa only [nextSource] using nextTypes
  · have finalFuncs := (finalMetadata.resolve nextFound).functions.trans (elementMetadata.resolve elementFound).functions
    have finalExterns := finalStaged.externs.trans globalStaged.externs.symm
    simpa only [GlobalContents, GlobalShape, ReferenceShape, finalGlobals, elementGlobals, finalFuncs, finalExterns] using globalsCanonical
  · simpa [nextGlobalMap, elementGlobalMap] using globalCount rfl
  · have size := (nextTypes).length_eq
    simpa only [elementSource, globalSource, alloc.vec.Vec.length] using size.symm
  · simpa [elementEmpty, elementSource, globalSource] using finalCount rfl

  · have finalIdentity := (finalMetadata.resolve nextFound).identity.trans (elementMetadata.resolve elementFound).identity
    simpa only [nextGlobalMap, elementGlobalMap, finalIdentity, finalGlobals, elementGlobals] using nextGlobalIssued

  · exact (globalMetadata.resolve globalFound).trans ((elementMetadata.resolve elementFound).trans (finalMetadata.resolve nextFound))
  · simpa only [nextSource] using nextTypes

end Exec.Store
