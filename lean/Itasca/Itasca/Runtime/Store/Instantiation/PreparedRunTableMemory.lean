import ItascaRust.Funs
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Api.AllocationLoops
import Itasca.Runtime.Store.Initialization.SegmentLoops
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Store.Invariant.ObjectAllocationErrors
import Itasca.Runtime.Store.Invariant.SourceAllocationLists
import Itasca.Runtime.Store.Definitions
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Initialization.SegmentOperations
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions

/-!
Proofs for Runtime / Store / Instantiation.

This module collects StagingCommitShape, PreparedRunTableMemory.
Each section documents its contracts and consumers.
-/

/-! ## StagingCommitShape -/

section

/-!
Proofs for Runtime / Store / Preparation.

This module collects StagingSegmentBounds, StagingCommitShape.
Each section documents its contracts and consumers.
-/

/-! ## StagingSegmentBounds -/

section

/-! ## StagingGlobalTypes -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Successful actual global, element, and data staging constructs the source/raw
segment type bindings and preserves every issued element reference. The initial
empty segment maps come from publication of the newly prepared instance. -/
theorem staging_global_types {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (importTypes : List Itasca.wasm_types.GlobalType)
    (globalMatching : GlobalTypeMap store importTypes inst.globals.val)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      InitializerFunctionMetadata store inst after next ∧
      GlobalTypeMap after (importTypes ++ inst.module.module.env.globals.val.map Itasca.metadata.Global.gtype) next.globals.val ∧
      ElementTypeMap after inst.module.module.env.elements.val next.elems.val := by
  have globals := global_type_staging_loop memory hooks floats allocator law before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound (by simp) (by simpa using globalCapacity) importTypes (by simpa using globalMatching)
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap, globalTypes⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have globalEmpty : globalInst.elems.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elems.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements := element_global_type_staging_loop memory hooks floats allocator law before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound
    (by simp) elementRoom mapRoom
    (importTypes ++ inst.module.module.env.globals.val.map Itasca.metadata.Global.gtype) (globalTypes rfl) (fun _ => initialTypes)
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes, elementGlobals⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have elementEmpty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data := data_global_type_staging_loop memory allocator law before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound
    (by simp) dataRoom dataMapRoom
    (importTypes ++ inst.module.module.env.globals.val.map Itasca.metadata.Global.gtype) elementGlobals
    (by simpa only [elementSource] using elementTypes rfl)
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalAccounted, finalMetadata,
    next, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextTypes, nextGlobals⟩ := data
  obtain ⟨rfl, rfl⟩ := (store_state_parts_inj _ _ _ _).mp result
  refine ⟨next, nextFound, nextSource.trans (elementSource.trans globalSource), ?_, nextGlobals, ?_⟩
  · exact (globalMetadata.resolve globalFound).trans
      ((elementMetadata.resolve elementFound).trans (finalMetadata.resolve nextFound))
  · simpa only [nextSource, elementSource, globalSource] using nextTypes

end Itasca.Store

end

/-! ## StagingSegmentBounds -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Successful actual global, element, and data staging constructs the source/raw
segment type bindings and preserves every issued element reference. The initial
empty segment maps come from publication of the newly prepared instance. -/
theorem staging_segment_bounds {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (bounded : SegmentBounds store)
    (elementBounds : ∀ element ∈ inst.module.module.env.elements.val, element.init.length < 2^32)
    (dataBounds : ∀ data ∈ inst.module.module.tail.data.val, data.init.length < 2^32)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    SegmentBounds after := by
  have globals := global_content_staging_loop memory hooks floats allocator law before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound (by simp) (by simpa using globalCapacity)
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalsCanonical, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap, globalCount⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have globalBounds : SegmentBounds globalStore := bounded.same globalElements globalData
  have globalEmpty : globalInst.elems.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elems.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements := element_bounds_staging_loop memory hooks floats allocator law before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound
    (by simp) elementRoom mapRoom (fun _ => initialTypes) globalBounds
    (by simpa only [globalSource] using elementBounds)
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementBoundsAfter, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have elementEmpty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data := data_bounds_staging_loop memory allocator law before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound
    (by simp) dataRoom dataMapRoom elementBoundsAfter
    (by simpa only [elementSource, globalSource] using dataBounds)
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalBounds, rest⟩ := data
  obtain ⟨rfl, rfl⟩ := (store_state_parts_inj _ _ _ _).mp result
  exact finalBounds

end Itasca.Store

end

end

/-! ## StagingCommitShape -/

section

open Itasca.Representation

/-!
Store shape at staging commit. Allocation certificates and issued ownership establish staged instance shape and the final committed-store invariant.
-/

/-! ## Staging Allocation -/

section

namespace Itasca.Store
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
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (allocated : AllocationShape view store)
    (globalIssued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      SegmentTypeBindings after next ∧ ElementContents after ∧ GlobalContents after ∧
      next.globals.length = inst.globals.length + inst.module.module.env.globals.val.length ∧
      next.elems.length = inst.module.module.env.elements.val.length ∧
      next.datas.length = inst.module.module.tail.data.val.length ∧
      (∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length) ∧
      (∀ address ∈ next.datas.val, address.val < after.datas.length) ∧
      InitializerFunctionMetadata store inst after next ∧
      ElementTypeMap after next.module.module.env.elements.val next.elems.val ∧ AllocationShape view after ∧
      StagedPrefix before after ∧ (SegmentAccounting store → SegmentAccounting after) := by
  have contents : ElementContents store := allocated.elements
  have globals := global_allocated_loop memory hooks floats allocator law view before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound allocated (by simp) (by simpa using globalCapacity) globalIssued
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalAllocated, globalsCanonical, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, nextGlobalIssued, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap, globalCount⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have globalTables := (globalMetadata.resolve globalFound).table_types tables
  have globalContents : ElementContents globalStore := by
    have funcs := (globalMetadata.resolve globalFound).functions
    have externs := globalStaged.externs.trans staged.externs.symm
    simpa only [ElementContents, ReferenceShape, globalElements, funcs, externs] using contents
  have globalEmpty : globalInst.elems.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elems.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements := element_allocated_loop memory hooks floats allocator law view before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound globalAllocated
    (by simp) elementRoom mapRoom (fun _ => initialTypes) globalContents
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementAllocated, elementContents, elementGlobals, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementGlobalMap, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have elementTables := (elementMetadata.resolve elementFound).table_types globalTables
  have elementEmpty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data := data_allocated_loop memory allocator law view before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound elementAllocated
    (by simp) dataRoom dataMapRoom (by simpa only [elementSource] using elementTypes rfl) elementContents (by simp [elementEmpty])
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalAllocated, finalContents, finalGlobals, finalAccounted, finalMetadata,
    next, nextFound, nextSource, nextDataIssued, nextGlobalMap, nextBindings, nextImports, nextSegments, nextTypes, finalCount⟩ := data
  obtain ⟨rfl, rfl⟩ := (store_state_parts_inj _ _ _ _).mp result
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

end Itasca.Store

end

/-! ## Staging Owned -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Successful actual global, element, and data staging constructs the source/raw
segment type bindings and preserves every issued element reference. The initial
empty segment maps come from publication of the newly prepared instance. -/
theorem staging_owned_certificates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (contents : ElementContents store)
    (globalIssued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      SegmentTypeBindings after next ∧ ElementContents after ∧ GlobalContents after ∧
      next.globals.length = inst.globals.length + inst.module.module.env.globals.val.length ∧
      next.elems.length = inst.module.module.env.elements.val.length ∧
      next.datas.length = inst.module.module.tail.data.val.length ∧
      (∀ address ∈ next.globals.val, address.store = after.id ∧ address.index.val < after.globals.length) ∧
      (∀ address ∈ next.datas.val, address.val < after.datas.length) ∧
      InitializerFunctionMetadata store inst after next ∧
      ElementTypeMap after next.module.module.env.elements.val next.elems.val := by
  have globals := global_owned_staging_loop memory hooks floats allocator law before store platform index 0#usize inst (.Ok ())
    staged fresh found compiled valid.globals bindings imports segments objectBound (by simp) (by simpa using globalCapacity) globalIssued
  rw [globalRun] at globals
  simp only [WP.spec_ok] at globals
  obtain ⟨actual, status, result, globalStaged, globalBound, globalsCanonical, globalAccounted, globalMetadata,
    globalInst, globalFound, globalSource, nextGlobalIssued, globalBindings, globalImports, globalSegments,
    globalElements, globalData, globalElementMap, globalDataMap, globalCount⟩ := globals
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have globalTables := (globalMetadata.resolve globalFound).table_types tables
  have globalContents : ElementContents globalStore := by
    have funcs := (globalMetadata.resolve globalFound).functions
    have externs := globalStaged.externs.trans staged.externs.symm
    simpa only [ElementContents, ReferenceShape, globalElements, funcs, externs] using contents
  have globalEmpty : globalInst.elems.val = [] := by rw [globalElementMap, emptyElements]
  have initialTypes : ElementTypeMap globalStore (globalInst.module.module.env.elements.val.take 0#usize.val) globalInst.elems.val := by
    simp [ElementTypeMap, globalEmpty]
  have elementRoom : globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalElements, globalSource] using elementCapacity
  have mapRoom : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [globalEmpty, globalSource] using inst.module.module.env.elements.property
  have elements := element_complete_staging_loop memory hooks floats allocator law before globalStore platform index 0#usize globalInst (.Ok ())
    globalStaged fresh globalFound (by simpa only [globalSource] using compiled)
    (by simpa only [globalSource] using valid.elements) globalBindings globalImports globalSegments globalBound
    (by simp) elementRoom mapRoom (fun _ => initialTypes) globalContents
  rw [elementRun] at elements
  simp only [WP.spec_ok] at elements
  obtain ⟨actual, status, result, elementStaged, elementBound, elementContents, elementGlobals, elementAccounted, elementMetadata,
    elementInst, elementFound, elementSource, elementGlobalMap, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementTypes⟩ := elements
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp result
  have elementTables := (elementMetadata.resolve elementFound).table_types globalTables
  have elementEmpty : elementInst.datas.val = [] := by rw [elementDataMap, globalDataMap, emptyData]
  have dataRoom : elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementData, globalData, elementSource, globalSource] using dataCapacity
  have dataMapRoom : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0#usize.val) ≤ Usize.max := by
    simpa [elementEmpty, elementSource, globalSource] using inst.module.module.tail.data.property
  have data := data_owned_staging_loop memory allocator law before elementStore index 0#usize elementInst (.Ok ())
    elementStaged fresh elementFound elementBindings elementImports elementSegments elementBound
    (by simp) dataRoom dataMapRoom (by simpa only [elementSource] using elementTypes rfl) elementContents (by simp [elementEmpty])
  rw [dataRun] at data
  simp only [WP.spec_ok] at data
  obtain ⟨actual, status, result, finalStaged, finalBound, finalContents, finalGlobals, finalAccounted, finalMetadata,
    next, nextFound, nextSource, nextDataIssued, nextGlobalMap, nextBindings, nextImports, nextSegments, nextTypes, finalCount⟩ := data
  obtain ⟨rfl, rfl⟩ := (store_state_parts_inj _ _ _ _).mp result
  have finalTables := (finalMetadata.resolve nextFound).table_types elementTables
  refine ⟨next, nextFound, nextSource.trans (elementSource.trans globalSource), ?_, finalContents, ?_, ?_, ?_, ?_, ?_, nextDataIssued, ?_, ?_⟩
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

end Itasca.Store

end

/-! ## Staging Instance Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Successful actual initializer staging completes the new instance's structural
maps. Prepared type/function certificates and linked owner facts are transported
through the actual loops; source counts come from the canonical environment. -/
theorem staging_instance_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (contents : ElementContents store)
    (globalIssued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (preparedTypes : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (preparedFunctions : Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType))
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = (Itasca.Module.Environment.importedGlobals inst.module.module.env.imports.val).length)
    {sourceTables sourceMemories} (cache : Itasca.Module.Environment.Cache inst.module.module.env sourceTables sourceMemories)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      InstanceShape after next ∧ SegmentTypeBindings after next ∧
      ElementContents after ∧ GlobalContents after ∧ InitializerFunctionMetadata store inst after next := by
  obtain ⟨next, nextFound, source, types, elementContents, globalContents, globals, elements, datas,
    globalAddresses, dataAddresses, metadata, elementTypes⟩ := staging_owned_certificates memory hooks floats allocator law
      before store platform index inst staged fresh found compiled valid bindings imports segments objectBound
      globalCapacity elementCapacity dataCapacity emptyElements emptyData tables contents globalIssued
      globalStore elementStore after globalRun elementRun dataRun
  have finalTypes := metadata.type_entries preparedTypes
  have finalFunctions := metadata.function_table preparedFunctions
  have finalTables := metadata.table_types tables
  have finalOwners : ∀ address ∈ next.tables.val, address.store = after.id := by
    simpa only [metadata.tableMap, metadata.identity] using tableOwners
  have finalMemoryCount : next.memories.length = next.module.module.env.mem_types.length := by
    simpa only [metadata.memoryMap, source] using memoryCount
  have finalMemories : ∀ address ∈ next.memories.val, address.store = after.id ∧ address.index.val < after.memories.length := by
    simpa only [metadata.memoryMap, metadata.identity, metadata.memories] using memoryAddresses
  have finalGlobalCount : next.globals.length = next.module.module.env.global_types.length := by
    have sourceCount := congrArg List.length cache.globals
    simp only [List.length_append, List.length_map] at sourceCount
    rw [source]
    change next.globals.length = inst.module.module.env.global_types.val.length
    omega
  refine ⟨next, nextFound, source, ?_, types, elementContents, globalContents, metadata⟩
  apply instance_shape_of_maps after next
    (by simpa only [source] using finalTypes) (by simpa only [source] using finalFunctions)
    (by simpa only [source] using finalTables) finalOwners finalMemoryCount finalMemories finalGlobalCount
    globalAddresses elementTypes (by simpa only [source] using datas) dataAddresses

end Itasca.Store

end

/-! ## Staging Commit Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The actual initializer staging sequence establishes the full store invariant
at the commit point after the checked source-derived item charge. -/
theorem staging_commit_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (platform : P) (index : Usize)
    (inst : runtime.store.ModuleInst)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ index.val)
    (found : store.instances.val[index.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : Itasca.Module.Environment.Valid inst.module.module.env)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max)
    (elementCapacity : store.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : store.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = [])
    (tables : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val)
    (allocated : AllocationShape view store)
    (globalIssued : ∀ address ∈ inst.globals.val, address.store = store.id ∧ address.index.val < store.globals.length)
    (preparedTypes : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (preparedFunctions : Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType))
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = (Itasca.Module.Environment.importedGlobals inst.module.module.env.imports.val).length)
    {sourceTables sourceMemories} (cache : Itasca.Module.Environment.Cache inst.module.module.env sourceTables sourceMemories)
    (oldShape : Shape view before) (indexEq : index = before.instances.len)
    (initialCount : store.instances.length = before.instances.length + 1)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (stagedFunctions : StagedFunctionSignatures before store index
      (inst.module.module.env.func_types.val.drop (Itasca.Module.Environment.importedFuncs inst.module.module.env.imports.val).length))
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems inst.module)
    (limited : count.val ≤ before.limits.max_instance_items.val)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[index.val]? = some next ∧ next.module = inst.module ∧
      Shape view {after with instance_items := count} ∧ SegmentTypeBindings after next ∧
      InitializerFunctionMetadata store inst after next ∧ StagedPrefix before after ∧
      (SegmentAccounting store → SegmentAccounting after) := by
  subst index
  have contents : ElementContents store := allocated.elements
  obtain ⟨next, nextFound, source, types, elementContents, globalContents, globals, elements, datas,
    globalAddresses, dataAddresses, metadata, elementTypes, finalAllocated, retained, accounting⟩ :=
    staging_allocated_certificates memory hooks floats allocator law view before store platform before.instances.len inst
      staged fresh found compiled valid bindings imports segments objectBound
      globalCapacity elementCapacity dataCapacity emptyElements emptyData tables allocated globalIssued
      globalStore elementStore after globalRun elementRun dataRun
  obtain ⟨actual, actualFound, actualSource, actualShape, _⟩ :=
    staging_instance_shape memory hooks floats allocator law before store platform before.instances.len inst
      staged fresh found compiled valid bindings imports segments objectBound
      globalCapacity elementCapacity dataCapacity emptyElements emptyData tables contents globalIssued
      preparedTypes preparedFunctions tableOwners memoryCount memoryAddresses globalCount cache
      globalStore elementStore after globalRun elementRun dataRun
  have same : actual = next := Option.some.inj (actualFound.symm.trans nextFound)
  subst actual
  have finalFunctions := metadata.staged_functions stagedFunctions
  refine ⟨next, nextFound, source, ?_, types, metadata, retained, accounting⟩
  apply shape_after_staging view before after oldShape finalAllocated retained next nextFound actualShape
    (metadata.instanceCount.trans initialCount) instanceRoom
    (by simpa only [source] using cache)
    (by simpa only [source] using finalFunctions) count
    (by simpa only [source] using counted)
    (by simpa only [retained.limits] using limited)

end Itasca.Store

end

end

end

/-! ## PreparedRunTableMemory -/

section

/-!
Proofs for Runtime / Store / Instantiation.

This module collects PrecommitOrigins, PreparedRunTableMemory.
Each section documents its contracts and consumers.
-/

/-! ## PrecommitOrigins -/

section

open Itasca.Representation

/-! ## PublishInstance -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The actual vector publication after preparation adds one fresh provisional
instance. It does not yet claim that the incomplete instance has full Shape. -/
theorem publish_prepared_instance {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (room : store.instances.length < Usize.max)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (accounted : SegmentAccounting store)
    (emptyElements : inst.elems.val = []) (emptyData : inst.datas.val = []) :
    alloc.vec.Vec.push store.instances inst ⦃ instances =>
      let after := {store with instances}
      instances.val = store.instances.val ++ [inst] ∧
      after.instances.val[store.instances.len.val]? = some inst ∧ StagedPrefix store after ∧
      InitializerBindings after inst ∧ InitializerImports after inst ∧ InitializerSegmentBindings after inst ∧
      SegmentAccounting after ∧ objectCount after = objectCount store ⦄ := by
  step as ⟨instances, appended⟩
  refine ⟨appended, ?_, ?_, ⟨bindings.funcs, bindings.globals⟩, ⟨imports.funcs, imports.globals⟩,
    ⟨segments.tableCount, segments.memoryCount, segments.tables, segments.memories⟩, ?_, rfl⟩
  · simp [appended]
  · constructor <;> simp [appended]
  · apply accounted.append_instance inst appended
    · simp [emptyElements]
    · simp [emptyData]

end Itasca.Store

end

/-! ## PreparedCommitShape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_shape {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env)
    (compiled : Compiler.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems seed.module)
    (limited : count.val ≤ before.limits.max_instance_items.val)
    (typed functions tabled prepared : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts prepared (.Ok ()) inst))
    (publishedInstances : alloc.vec.Vec runtime.store.ModuleInst)
    (publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
      {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[before.instances.len.val]? = some next ∧ next.module = seed.module ∧
      Shape view {after with instance_items := count} ∧ SegmentTypeBindings after next ∧
      StagedPrefix before after ∧ SegmentAccounting after ∧
      InstantiationCode before {after with instance_items := count} next := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨preparedTypes, preparedFunctions, signatures⟩ :=
    preparation_certificates memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨preparedTables, tableAddresses, memoryAddresses, memoryCount, allocated⟩ :=
    preparation_allocated_maps memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  have room : prepared.instances.length < Usize.max := by
    rw [preparedInstances]
    scalar_tac
  have preparedAccounting : SegmentAccounting prepared := by
    constructor
    · simpa only [preparedElements, preparedInstances] using accounted.elements
    · simpa only [preparedData, preparedInstances] using accounted.datas
  have emptyElements : inst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
  have emptyData : inst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
  have publication := publish_prepared_instance prepared inst room preparedBindings preparedImports preparedSegments
    preparedAccounting emptyElements emptyData
  rw [publicationRun] at publication
  simp only [WP.spec_ok] at publication
  obtain ⟨appended, publishedFound, publishedPrefix, publishedBindings, publishedImports, publishedSegments,
    publishedAccounting, publishedObjects⟩ := publication
  let published := {prepared with instances := publishedInstances}
  have found : published.instances.val[before.instances.len.val]? = some inst := by
    simpa only [preparedInstances] using publishedFound
  have globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max := by
    simpa only [preparedGlobalMap, preparedSource] using maps.global_capacity cache
  have elementRoom : published.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max := by
    simpa only [published, preparedElements, preparedSource] using elementCapacity
  have dataRoom : published.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max := by
    simpa only [published, preparedData, preparedSource] using dataCapacity
  have globalIssued : ∀ address ∈ inst.globals.val, address.store = published.id ∧ address.index.val < published.globals.length := by
    simpa only [published, preparedGlobalMap, preparedGlobals, preparedPrefix.identity] using maps.globals_owned
  have importedCount : inst.globals.length = (importedGlobals inst.module.module.env.imports.val).length := by
    simpa only [preparedGlobalMap, preparedSource] using maps.globals.length_eq.symm
  have publishedFunctions := function_table_prefix publishedPrefix preparedFunctions
  have publishedTypes := preparedTypes.extend publishedPrefix
  have publishedSignatures := signatures.extend publishedPrefix rfl
  obtain ⟨next, nextFound, source, shaped, types, metadata, retained, countedSegments⟩ :=
    staging_commit_shape memory hooks floats allocator law view before published platform before.instances.len inst
      (preparedPrefix.trans publishedPrefix) (by simp) found
      (by simpa only [preparedSource] using compiled)
      (by simpa only [preparedSource] using valid)
      publishedBindings publishedImports publishedSegments
      (by change objectCount prepared ≤ Usize.max; exact preparedBound)
      globalCapacity elementRoom dataRoom emptyElements emptyData
      (by simpa only [TableTypeMap, published] using preparedTables)
      (allocated.replace_instances publishedInstances) globalIssued
      (by simpa only [preparedSource] using publishedTypes)
      (by simpa only [preparedSource] using publishedFunctions)
      (fun address member => (tableAddresses address member).1) memoryCount memoryAddresses importedCount
      (by simpa only [preparedSource] using cache) shape rfl
      (by simp [published, appended, preparedInstances]) instanceRoom
      (by simpa only [preparedSource] using publishedSignatures) count
      (by simpa only [preparedSource] using counted) limited
      globalStore elementStore after globalRun elementRun dataRun
  refine ⟨next, nextFound, source.trans preparedSource, shaped, types, retained,
    countedSegments publishedAccounting, after, count, rfl, retained, ?_, ?_, ?_⟩
  · simpa only [source, preparedSource] using metadata.type_entries publishedTypes
  · simpa only [source, preparedSource] using metadata.function_table publishedFunctions
  · simpa only [source, preparedSource] using metadata.staged_functions publishedSignatures

end Itasca.Store

end

/-! ## PreparedRun -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The concrete preparation and staging calls that produced a committed store.
This record contains actual call equalities and static link/capacity facts; it
contains no interpreter simulation or compiler-correctness premise. -/
structure PreparedRun {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (platform : P) (ready : runtime.store.Store M) where
  seed : runtime.store.ModuleInst
  source : seed.module = module
  maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed
  instanceRoom : before.instances.length < before.limits.max_instances.val
  elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max
  dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max
  typed : runtime.store.Store M
  functions : runtime.store.Store M
  tabled : runtime.store.Store M
  prepared : runtime.store.Store M
  typeInst : runtime.store.ModuleInst
  funcInst : runtime.store.ModuleInst
  tableInst : runtime.store.ModuleInst
  inst : runtime.store.ModuleInst
  typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
    .ok (typeParts typed (.Ok ()) typeInst)
  functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
    .ok (typeParts functions (.Ok ()) funcInst)
  tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
    .ok (typeParts tabled (.Ok ()) tableInst)
  memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
    .ok (typeParts prepared (.Ok ()) inst)
  publishedInstances : alloc.vec.Vec runtime.store.ModuleInst
  publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances
  globalStore : runtime.store.Store M
  elementStore : runtime.store.Store M
  dataStore : runtime.store.Store M
  globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
    {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
    .ok (storeParts globalStore platform (.Ok ()))
  elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
    .ok (storeParts elementStore platform (.Ok ()))
  dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
    .ok (storeStateParts dataStore (.Ok ()))
  charged : Usize
  counted : charged.val = before.instance_items.val + moduleItems seed.module
  limited : charged.val ≤ before.limits.max_instance_items.val
  committed : ready = {dataStore with instance_items := charged}
end Itasca.Store

end

/-! ## LinkedPreparedRun -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Preparation additionally retains the actual import-linking computation.
The supplied externals remain the caller's exact list, rather than an inferred
list satisfying only the final module's import types. -/
structure LinkedPreparedRun {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (platform : P) (ready : runtime.store.Store M)
    extends PreparedRun memory hooks floats allocator view before module platform ready where
  importsLength : imports.length = module.module.env.imports.length
  linkRun : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
    (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Ok (), seed)
end Itasca.Store

end

/-! ## PrecommitOrigins -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- A Link rejection originates at the public import-count gate or the actual
import loop, starting from the fresh instance's empty address maps. -/

def PrecommitLinkEvidence {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (error : runtime.ExecError) : Prop :=
  ∀ link, error = .Link link →
    (link = .MissingImport ∧ imports.length ≠ module.module.env.imports.length) ∨
    ∃ inst, runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err (.Link link), inst)

/-- Linking provenance of an actual precommit rejection. -/
structure PrecommitOrigins {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (before staged : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (error : runtime.ExecError) : Prop where
  linking : PrecommitLinkEvidence memory before module imports error

theorem PrecommitOrigins.resource {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (resource : ResourceError error) : PrecommitOrigins memory view before staged module imports error := by
  cases error <;> simp_all only [ResourceError]
  constructor
  intro link impossible
  cases impossible

theorem PrecommitOrigins.linked {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (inst : runtime.store.ModuleInst)
    (linked : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err error, inst))
    : PrecommitOrigins memory view before staged module imports error := by
  constructor
  intro link same
  exact Or.inr ⟨inst, same ▸ linked⟩

end Itasca.Store

end

end

/-! ## PreparedRunTableMemory -/

section

open Itasca.Representation

/-!
# Prepared Run Table Memory

Prepared globals, segments, tables and memories retain their source certificates. Shape and allocation facts support the complete prepared-run relation.
-/

/-! ## PreparedGlobalTypes -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_global_types {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env)
    (compiled : Compiler.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (typed functions tabled prepared : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts prepared (.Ok ()) inst))
    (publishedInstances : alloc.vec.Vec runtime.store.ModuleInst)
    (publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
      {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[before.instances.len.val]? = some next ∧
      next.module = seed.module ∧
      after.instances.length = before.instances.length + 1 ∧
      GlobalTypeMap after seed.module.module.env.global_types.val next.globals.val ∧
      ElementTypeMap after seed.module.module.env.elements.val next.elems.val := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  have room : prepared.instances.length < Usize.max := by
    rw [preparedInstances]
    scalar_tac
  have preparedAccounting : SegmentAccounting prepared := by
    constructor
    · simpa only [preparedElements, preparedInstances] using accounted.elements
    · simpa only [preparedData, preparedInstances] using accounted.datas
  have emptyElements : inst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
  have emptyData : inst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
  have publication := publish_prepared_instance prepared inst room preparedBindings preparedImports preparedSegments
    preparedAccounting emptyElements emptyData
  rw [publicationRun] at publication
  simp only [WP.spec_ok] at publication
  obtain ⟨appended, publishedFound, publishedPrefix, publishedBindings, publishedImports, publishedSegments,
    publishedAccounting, publishedObjects⟩ := publication
  let published := {prepared with instances := publishedInstances}
  have found : published.instances.val[before.instances.len.val]? = some inst := by
    simpa only [preparedInstances] using publishedFound
  have globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max := by
    simpa only [preparedGlobalMap, preparedSource] using maps.global_capacity cache
  have elementRoom : published.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max := by
    simpa only [published, preparedElements, preparedSource] using elementCapacity
  have dataRoom : published.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max := by
    simpa only [published, preparedData, preparedSource] using dataCapacity
  have imported : GlobalTypeMap prepared (importedGlobals seed.module.module.env.imports.val) inst.globals.val := by
    rw [preparedGlobalMap]
    exact GlobalTypeMap.prefix maps.globals preparedPrefix.identity preparedPrefix.globals
  have publishedTypes : GlobalTypeMap published (importedGlobals seed.module.module.env.imports.val) inst.globals.val := by
    exact imported
  obtain ⟨next, nextFound, nextSource, metadata, globals, elements⟩ :=
    staging_global_types memory hooks floats allocator law before published platform before.instances.len inst
      (preparedPrefix.trans publishedPrefix) (by simp) found
      (by simpa only [preparedSource] using compiled)
      (by simpa only [preparedSource] using valid)
      publishedBindings publishedImports publishedSegments
      (by change objectCount prepared ≤ Usize.max; exact preparedBound)
      globalCapacity elementRoom dataRoom emptyElements emptyData
      (importedGlobals seed.module.module.env.imports.val) publishedTypes
      globalStore elementStore after globalRun elementRun dataRun
  refine ⟨next, nextFound, nextSource.trans preparedSource, ?_, ?_, ?_⟩
  · rw [metadata.instanceCount]
    change publishedInstances.length = before.instances.length + 1
    simp only [alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
    rw [← alloc.vec.Vec.length, preparedInstances]
  · simpa only [cache.globals, preparedSource] using globals
  · simpa only [preparedSource] using elements

end Itasca.Store

end

/-! ## PreparedSegmentBounds -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_segment_bounds {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    (elementBounds : ∀ element ∈ seed.module.module.env.elements.val, element.init.length < 2^32)
    (dataBounds : ∀ data ∈ seed.module.module.tail.data.val, data.init.length < 2^32)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env)
    (compiled : Compiler.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (typed functions tabled prepared : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts prepared (.Ok ()) inst))
    (publishedInstances : alloc.vec.Vec runtime.store.ModuleInst)
    (publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
      {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
      .ok (storeStateParts after (.Ok ()))) :
    SegmentBounds after := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  have room : prepared.instances.length < Usize.max := by
    rw [preparedInstances]
    scalar_tac
  have preparedAccounting : SegmentAccounting prepared := by
    constructor
    · simpa only [preparedElements, preparedInstances] using accounted.elements
    · simpa only [preparedData, preparedInstances] using accounted.datas
  have emptyElements : inst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
  have emptyData : inst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
  have publication := publish_prepared_instance prepared inst room preparedBindings preparedImports preparedSegments
    preparedAccounting emptyElements emptyData
  rw [publicationRun] at publication
  simp only [WP.spec_ok] at publication
  obtain ⟨appended, publishedFound, publishedPrefix, publishedBindings, publishedImports, publishedSegments,
    publishedAccounting, publishedObjects⟩ := publication
  let published := {prepared with instances := publishedInstances}
  have found : published.instances.val[before.instances.len.val]? = some inst := by
    simpa only [preparedInstances] using publishedFound
  have globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max := by
    simpa only [preparedGlobalMap, preparedSource] using maps.global_capacity cache
  have elementRoom : published.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max := by
    simpa only [published, preparedElements, preparedSource] using elementCapacity
  have dataRoom : published.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max := by
    simpa only [published, preparedData, preparedSource] using dataCapacity
  apply staging_segment_bounds memory hooks floats allocator law before published platform before.instances.len inst
    (preparedPrefix.trans publishedPrefix) (by simp) found
    (by simpa only [preparedSource] using compiled)
    (by simpa only [preparedSource] using valid)
    publishedBindings publishedImports publishedSegments
    (by change objectCount prepared ≤ Usize.max; exact preparedBound)
    globalCapacity elementRoom dataRoom emptyElements emptyData
    (bounded.same preparedElements preparedData)
    (by simpa only [preparedSource] using elementBounds)
    (by simpa only [preparedSource] using dataBounds)
    globalStore elementStore after globalRun elementRun dataRun

end Itasca.Store

end

/-! ## PreparedRunCertificates -/

section

/-!
Prepared instance segment bounds, global types and store shape from compiler certificates. The PreparedRun relation remains separate for consumers that do not need compiler semantic proofs.
-/

/-! ## Prepared Run Bounds -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem PreparedRun.segment_bounds {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    {tables memories} (cache : Itasca.Module.Environment.Cache module.module.env tables memories)
    (valid : Itasca.Module.Environment.Valid module.module.env)
    (compiled : Compiler.InitializerMappings module)
    (elementBounds : ∀ element ∈ module.module.env.elements.val, element.init.length < 2^32)
    (dataBounds : ∀ data ∈ module.module.tail.data.val, data.init.length < 2^32) : SegmentBounds ready := by
  have prepared := prepared_commit_segment_bounds memory hooks floats allocator law view laws before trace.seed platform
    shape accounted bounded (by simpa only [trace.source] using elementBounds)
    (by simpa only [trace.source] using dataBounds) trace.maps
    (by simpa only [trace.source] using cache) (by simpa only [trace.source] using valid)
    (by simpa only [trace.source] using compiled) trace.instanceRoom trace.elementCapacity trace.dataCapacity
    trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
    trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
    trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  rw [trace.committed]
  exact prepared.same rfl rfl

/-- Actual successful compilation discharges every source-count obligation of
preparation; the retained call trace then transports the old store bounds. -/
theorem PreparedRun.compiled_segment_bounds {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module)) : SegmentBounds ready := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, _⟩ := witness.semantic law
  have actualValid : Itasca.Module.Environment.Valid module.module.env := by
    exact valid
  obtain ⟨elementBounds, dataBounds⟩ := Compiler.compile_segment_payload_bounds allocator law bytes limits module accepted
  exact trace.segment_bounds laws law shape accounted bounded cache actualValid certificates.2.2 elementBounds dataBounds
end Itasca.Store

end

/-! ## Prepared Run Global Types -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem PreparedRun.global_types {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Itasca.Module.Environment.Cache module.module.env tables memories)
    (valid : Itasca.Module.Environment.Valid module.module.env)
    (compiled : Compiler.InitializerMappings module) : ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      ready.instances.length = before.instances.length + 1 ∧
      GlobalTypeMap ready module.module.env.global_types.val inst.globals.val ∧
      ElementTypeMap ready module.module.env.elements.val inst.elems.val := by
  obtain ⟨inst, found, source, count, globals, elements⟩ := prepared_commit_global_types memory hooks floats allocator law view laws before trace.seed platform
    shape accounted trace.maps
    (by simpa only [trace.source] using cache) (by simpa only [trace.source] using valid)
    (by simpa only [trace.source] using compiled) trace.instanceRoom trace.elementCapacity trace.dataCapacity
    trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
    trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
    trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  rw [trace.committed]
  exact ⟨inst, found, source.trans trace.source, count, by
    simpa only [trace.source] using globals.prefix
      (after := {trace.dataStore with instance_items := trace.charged}) rfl (by simp),
    by simpa only [trace.source, ElementTypeMap] using elements⟩

end Itasca.Store

end

/-! ## Prepared Run Shape -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

theorem PreparedRun.shape_data {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Itasca.Module.Environment.Cache module.module.env tables memories)
    (valid : Itasca.Module.Environment.Valid module.module.env)
    (compiled : Compiler.InitializerMappings module) : ∃ inst, trace.dataStore.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      Shape view ready ∧ SegmentTypeBindings trace.dataStore inst ∧
      StagedPrefix before trace.dataStore ∧ SegmentAccounting trace.dataStore ∧
      InstantiationCode before ready inst := by
  obtain ⟨inst, found, source, shaped, segments, retained, segmentAccounting, code⟩ :=
    prepared_commit_shape memory hooks floats allocator law view laws before trace.seed platform
      shape accounted trace.maps (by simpa only [trace.source] using cache)
      (by simpa only [trace.source] using valid) (by simpa only [trace.source] using compiled)
      trace.instanceRoom trace.elementCapacity trace.dataCapacity trace.charged trace.counted trace.limited
      trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
      trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
      trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  exact ⟨inst, found, source.trans trace.source, by simpa only [trace.committed] using shaped,
    segments, retained, segmentAccounting, by simpa only [trace.committed] using code⟩
end Itasca.Store

end

end

/-! ## PreparedRunTableMemory -/

section

/-!
Prepared-run table and memory allocation certificates. Publication boundaries and the resolved, unexecuted start function remain explicit.
-/

/-! ## Prepared Run Table Memory -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

/-- Compose the actual preparation, publication, and initializer calls through
the committed item charge. All newly allocated object/map obligations are
constructed from these calls and the source environment's canonical cache. -/
theorem prepared_commit_table_memory_bindings {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (valid : Valid seed.module.module.env)
    (compiled : Compiler.InitializerMappings seed.module)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (elementCapacity : before.elems.length + seed.module.module.env.elements.val.length ≤ Usize.max)
    (dataCapacity : before.datas.length + seed.module.module.tail.data.val.length ≤ Usize.max)
    (count : Usize) (counted : count.val = before.instance_items.val + moduleItems seed.module)
    (limited : count.val ≤ before.limits.max_instance_items.val)
    (typed functions tabled prepared : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst before.instances.len =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts prepared (.Ok ()) inst))
    (publishedInstances : alloc.vec.Vec runtime.store.ModuleInst)
    (publicationRun : alloc.vec.Vec.push prepared.instances inst = .ok publishedInstances)
    (globalStore elementStore after : runtime.store.Store M)
    (globalRun : runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
      {prepared with instances := publishedInstances} platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize before.instances.len =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.prepare_instance_loop9 memory allocator elementStore (.Ok ()) 0#usize before.instances.len =
      .ok (storeStateParts after (.Ok ()))) :
    ∃ next, after.instances.val[before.instances.len.val]? = some next ∧ next.module = seed.module ∧
      TableBindings after next.module.module.env.table_types.val next.tables.val ∧
      MemoryBindings view after next.module.module.env.mem_types.val next.memories.val := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨preparedTypes, preparedFunctions, signatures⟩ :=
    preparation_certificates memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨preparedTables, tableAddresses, memoryAddresses, memoryCount, allocated⟩ :=
    preparation_allocated_maps memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  obtain ⟨fullTables, fullMemories⟩ :=
    preparation_table_memory_bindings memory allocator law view laws before seed shape maps cache before.instances.len
      typed functions tabled prepared typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  have room : prepared.instances.length < Usize.max := by
    rw [preparedInstances]
    scalar_tac
  have preparedAccounting : SegmentAccounting prepared := by
    constructor
    · simpa only [preparedElements, preparedInstances] using accounted.elements
    · simpa only [preparedData, preparedInstances] using accounted.datas
  have emptyElements : inst.elems.val = [] := by rw [preparedElementMap]; exact maps.elements
  have emptyData : inst.datas.val = [] := by rw [preparedDataMap]; exact maps.data
  have publication := publish_prepared_instance prepared inst room preparedBindings preparedImports preparedSegments
    preparedAccounting emptyElements emptyData
  rw [publicationRun] at publication
  simp only [WP.spec_ok] at publication
  obtain ⟨appended, publishedFound, publishedPrefix, publishedBindings, publishedImports, publishedSegments,
    publishedAccounting, publishedObjects⟩ := publication
  let published := {prepared with instances := publishedInstances}
  have found : published.instances.val[before.instances.len.val]? = some inst := by
    simpa only [preparedInstances] using publishedFound
  have globalCapacity : inst.globals.length + inst.module.module.env.globals.val.length ≤ Usize.max := by
    simpa only [preparedGlobalMap, preparedSource] using maps.global_capacity cache
  have elementRoom : published.elems.length + inst.module.module.env.elements.val.length ≤ Usize.max := by
    simpa only [published, preparedElements, preparedSource] using elementCapacity
  have dataRoom : published.datas.length + inst.module.module.tail.data.val.length ≤ Usize.max := by
    simpa only [published, preparedData, preparedSource] using dataCapacity
  have globalIssued : ∀ address ∈ inst.globals.val, address.store = published.id ∧ address.index.val < published.globals.length := by
    simpa only [published, preparedGlobalMap, preparedGlobals, preparedPrefix.identity] using maps.globals_owned
  have importedCount : inst.globals.length = (importedGlobals inst.module.module.env.imports.val).length := by
    simpa only [preparedGlobalMap, preparedSource] using maps.globals.length_eq.symm
  have publishedFunctions := function_table_prefix publishedPrefix preparedFunctions
  have publishedTypes := preparedTypes.extend publishedPrefix
  have publishedSignatures := signatures.extend publishedPrefix rfl
  obtain ⟨next, nextFound, source, shaped, types, metadata, retained, countedSegments⟩ :=
    staging_commit_shape memory hooks floats allocator law view before published platform before.instances.len inst
      (preparedPrefix.trans publishedPrefix) (by simp) found
      (by simpa only [preparedSource] using compiled)
      (by simpa only [preparedSource] using valid)
      publishedBindings publishedImports publishedSegments
      (by change objectCount prepared ≤ Usize.max; exact preparedBound)
      globalCapacity elementRoom dataRoom emptyElements emptyData
      (by simpa only [TableTypeMap, published] using preparedTables)
      (allocated.replace_instances publishedInstances) globalIssued
      (by simpa only [preparedSource] using publishedTypes)
      (by simpa only [preparedSource] using publishedFunctions)
      (fun address member => (tableAddresses address member).1) memoryCount memoryAddresses importedCount
      (by simpa only [preparedSource] using cache) shape rfl
      (by simp [published, appended, preparedInstances]) instanceRoom
      (by simpa only [preparedSource] using publishedSignatures) count
      (by simpa only [preparedSource] using counted) limited
      globalStore elementStore after globalRun elementRun dataRun
  refine ⟨next, nextFound, source.trans preparedSource, ?_, ?_⟩
  · exact metadata.table_bindings (TableBindings.prefix fullTables rfl (by simp [published]))
  · exact metadata.memory_bindings (MemoryBindings.prefix fullMemories rfl (by simp [published]))

theorem PreparedRun.table_memory_bindings {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env) (compiled : Compiler.InitializerMappings module) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      TableBindings ready inst.module.module.env.table_types.val inst.tables.val ∧
      MemoryBindings view ready inst.module.module.env.mem_types.val inst.memories.val := by
  obtain ⟨inst, found, source, tableMap, memoryMap⟩ :=
    prepared_commit_table_memory_bindings memory hooks floats allocator law view laws before trace.seed platform
      shape accounted trace.maps (by simpa only [trace.source] using cache)
      (by simpa only [trace.source] using valid) (by simpa only [trace.source] using compiled)
      trace.instanceRoom trace.elementCapacity trace.dataCapacity trace.charged trace.counted trace.limited
      trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
      trace.typeRun trace.functionRun trace.tableRun trace.memoryRun trace.publishedInstances trace.publicationRun
      trace.globalStore trace.elementStore trace.dataStore trace.globalRun trace.elementRun trace.dataRun
  refine ⟨inst, ?_, source.trans trace.source, ?_, ?_⟩
  · simpa only [trace.committed] using found
  · rw [trace.committed]
    exact TableBindings.prefix tableMap rfl (by simp)
  · rw [trace.committed]
    exact MemoryBindings.prefix memoryMap rfl (by simp)

end Itasca.Store

end

/-! ## Prepared Run Table Memory Allocations -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Module.Environment

/-- The retained actual preparation calls allocate the source-defined table and
memory suffixes, with exact null/zero contents and consecutive fresh addresses. -/
theorem PreparedRun.table_memory_allocations {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories) :
    trace.prepared.tables.val.map decodeTable = before.tables.val.map decodeTable ++
      tables.map (fun ty => Spec.allocationTable (Itasca.Translation.Environment.tableType ty)) ∧
    trace.prepared.memories.val.map (decodeMemory view) = before.memories.val.map (decodeMemory view) ++
      memories.map (fun ty => Spec.allocationMemory (Itasca.Translation.Environment.memType ty)) ∧
    trace.inst.tables.val.map (fun address => address.index.val) =
      trace.seed.tables.val.map (fun address => address.index.val) ++ List.range' before.tables.length tables.length ∧
    trace.inst.memories.val.map (fun address => address.index.val) =
      trace.seed.memories.val.map (fun address => address.index.val) ++ List.range' before.memories.length memories.length ∧
    trace.prepared.tables.length = before.tables.length + tables.length ∧
    trace.prepared.memories.length = before.memories.length + memories.length := by
  exact preparation_table_memory_allocations memory allocator law view laws before trace.seed shape trace.maps
    (by simpa only [trace.source] using cache) before.instances.len trace.typed trace.functions trace.tabled trace.prepared
    trace.typeInst trace.funcInst trace.tableInst trace.inst trace.typeRun trace.functionRun trace.tableRun trace.memoryRun

/-- Table and memory allocation retain the exact function and signature
vectors and instance maps established by the preceding preparation stages. -/
theorem PreparedRun.preparation_metadata {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories) :
    trace.prepared.funcs = trace.functions.funcs ∧ trace.prepared.types = trace.typed.types ∧
    trace.inst.funcs = trace.funcInst.funcs ∧ trace.inst.types = trace.typeInst.types ∧
    trace.inst.module = module := by
  obtain ⟨_, _, _, _, _, _, functions, types, functionMap, typeMap, source⟩ :=
    preparation_table_memory_allocations_metadata memory allocator law view laws before trace.seed shape trace.maps
      (by simpa only [trace.source] using cache) before.instances.len trace.typed trace.functions trace.tabled trace.prepared
      trace.typeInst trace.funcInst trace.tableInst trace.inst trace.typeRun trace.functionRun trace.tableRun trace.memoryRun
  exact ⟨functions, types, functionMap, typeMap, source.trans trace.source⟩
end Itasca.Store

end

end

end

end
