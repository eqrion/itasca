import Itasca.Runtime.Store.Preparation.StagingTypeCertificates
import Itasca.Runtime.Store.Invariant.AllocatedGlobalLoop
import Itasca.Runtime.Store.Invariant.AllocatedElementLoop
import Itasca.Runtime.Store.Invariant.AllocatedDataLoop
import Itasca.Runtime.Store.Invariant.OwnedGlobalLoop
import Itasca.Runtime.Store.Initialization.ElementCompleteLoop
import Itasca.Runtime.Store.Invariant.OwnedDataLoop
import Itasca.Runtime.Store.Invariant.InstanceMapShape
import Itasca.Runtime.Store.Invariant.ShapeAssembly

/-!
Store shape at staging commit. Allocation certificates and issued ownership establish staged instance shape and the final committed-store invariant.
-/

/-! ## Staging Allocation -/

section

namespace Itasca.Runtime.Store
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
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
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
  have elements  := element_allocated_loop memory hooks floats allocator law view before globalStore platform index 0#usize globalInst (.Ok ())
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
  have data  := data_allocated_loop memory allocator law view before elementStore index 0#usize elementInst (.Ok ())
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

end Itasca.Runtime.Store

end

/-! ## Staging Owned -/

section

namespace Itasca.Runtime.Store
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
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
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

end Itasca.Runtime.Store

end

/-! ## Staging Instance Shape -/

section

namespace Itasca.Runtime.Store
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
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
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
    (preparedFunctions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = (Itasca.ModuleEnv.importedGlobals inst.module.module.env.imports.val).length)
    {sourceTables sourceMemories} (cache : Itasca.ModuleEnv.Cache inst.module.module.env sourceTables sourceMemories)
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

end Itasca.Runtime.Store

end

/-! ## Staging Commit Shape -/

section

namespace Itasca.Runtime.Store
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
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
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
    (preparedFunctions : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (tableOwners : ∀ address ∈ inst.tables.val, address.store = store.id)
    (memoryCount : inst.memories.length = inst.module.module.env.mem_types.length)
    (memoryAddresses : ∀ address ∈ inst.memories.val, address.store = store.id ∧ address.index.val < store.memories.length)
    (globalCount : inst.globals.length = (Itasca.ModuleEnv.importedGlobals inst.module.module.env.imports.val).length)
    {sourceTables sourceMemories} (cache : Itasca.ModuleEnv.Cache inst.module.module.env sourceTables sourceMemories)
    (oldShape : Shape view before) (indexEq : index = before.instances.len)
    (initialCount : store.instances.length = before.instances.length + 1)
    (instanceRoom : before.instances.length < before.limits.max_instances.val)
    (stagedFunctions : StagedFunctionSignatures before store index
      (inst.module.module.env.func_types.val.drop (Itasca.ModuleEnv.importedFuncs inst.module.module.env.imports.val).length))
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

end Itasca.Runtime.Store

end
