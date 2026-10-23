import Exec.Store.Preparation.StagingOwned
import Exec.Store.Invariant.InstanceMapShape

namespace Exec.Store
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
    (compiled : Code.InitializerMappings inst.module)
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
    (globalRun : runtime.store.instantiate.Store.instantiate_inner_loop7 memory hooks floats allocator store platform (.Ok ()) 0#usize index =
      .ok (storeParts globalStore platform (.Ok ())))
    (elementRun : runtime.store.instantiate.Store.instantiate_inner_loop8 memory hooks floats allocator globalStore platform (.Ok ()) 0#usize index =
      .ok (storeParts elementStore platform (.Ok ())))
    (dataRun : runtime.store.instantiate.Store.instantiate_inner_loop9 memory allocator elementStore (.Ok ()) 0#usize index =
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

end Exec.Store
