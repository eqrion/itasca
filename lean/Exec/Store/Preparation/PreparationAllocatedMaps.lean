import Exec.Store.Preparation.PreparationResults
import Exec.Store.Invariant.FunctionAllocatedPreparation
import Exec.Store.Invariant.AllocatedTypeLoop
import Exec.Store.Invariant.AllocatedTableLoop
import Exec.Store.Invariant.AllocatedMemoryLoop
import Exec.Store.Linking.LinkedOwners

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Successful actual preparation preserves imported table types and constructs
the exact source-to-raw type map for every newly allocated table. -/
theorem preparation_allocated_maps {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (instanceIndex : Usize)
    (typed functions tabled after : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.instantiate_inner_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.instantiate_inner_loop4 memory allocator typed (.Ok ()) 0#usize typeInst instanceIndex =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.instantiate_inner_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.instantiate_inner_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts after (.Ok ()) inst)) :
    TableTypeMap after inst.module.module.env.table_types.val inst.tables.val ∧
    (∀ address ∈ inst.tables.val, address.store = after.id ∧ address.index.val < after.tables.length) ∧
    (∀ address ∈ inst.memories.val, address.store = after.id ∧ address.index.val < after.memories.length) ∧
    inst.memories.length = inst.module.module.env.mem_types.val.length ∧ AllocationShape view after := by
  have objectBound : objectCount before ≤ Usize.max := by
    have bound := shape.objectLimit
    unfold objectCount
    scalar_tac
  have emptyTypes : TypeEntries before (seed.module.module.env.types.val.take 0) seed.types.val := by
    simp [TypeEntries, maps.types]
  have typeChecked  := type_allocated_loop memory allocator law view before before seed seed 0#usize
    (by simp) rfl rfl (.refl _) objectBound shape.allocated emptyTypes
  have typePost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ typeChecked typed typeInst (.Ok ()) typeRun
  obtain ⟨typeStore, typeMap, typePrefix, typeBound, typeAllocated, typeEntries⟩ := typePost
  have typeStore_funcs := congrArg runtime.store.Store.funcs typeStore
  dsimp only at typeStore_funcs
  have typeStore_tables := congrArg runtime.store.Store.tables typeStore
  dsimp only at typeStore_tables
  have typeStore_memories := congrArg runtime.store.Store.memories typeStore
  dsimp only at typeStore_memories
  have typeMap_module := congrArg runtime.store.ModuleInst.module typeMap
  dsimp only at typeMap_module
  have typeMap_tables := congrArg runtime.store.ModuleInst.tables typeMap
  dsimp only at typeMap_tables
  have typeMap_memories := congrArg runtime.store.ModuleInst.memories typeMap
  dsimp only at typeMap_memories
  have typeSource : typeInst.module = seed.module := by
    have h := congrArg runtime.store.ModuleInst.module typeMap
    exact h
  have typeFuncs : typeInst.funcs = seed.funcs := by
    have h := congrArg runtime.store.ModuleInst.funcs typeMap
    exact h
  have typeTable : Interp.FunctionTable typed typeInst
      ((typeInst.module.module.env.func_types.val.take (importedFuncs typeInst.module.module.env.imports.val).length).map decodeFuncType) := by
    have linkedTable := function_table_instance typeFuncs (function_table_prefix typePrefix (maps.function_table cache))
    simpa only [typeSource] using linkedTable
  have typeCache : Cache typeInst.module.module.env tables memories := by simpa only [typeSource] using cache
  have mappedTypes : TypeEntries typed typeInst.module.module.env.types.val typeInst.types.val := by
    simpa only [typeSource] using typeEntries rfl
  have functionChecked  := prepare_function_allocated memory allocator law view typed typeInst instanceIndex typeCache
    typeBound typeAllocated mappedTypes typeTable
  have functionPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ functionChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨functionStore, functionMap, functionPrefix, functionBound, functionAllocated, functionTable, staged⟩ := functionPost
  have functionIssued := function_table_issued (functionTable rfl)
  have functionStore_tables := congrArg runtime.store.Store.tables functionStore
  dsimp only at functionStore_tables
  have functionStore_memories := congrArg runtime.store.Store.memories functionStore
  dsimp only at functionStore_memories
  have functionMap_module := congrArg runtime.store.ModuleInst.module functionMap
  dsimp only at functionMap_module
  have functionMap_tables := congrArg runtime.store.ModuleInst.tables functionMap
  dsimp only at functionMap_tables
  have functionMap_memories := congrArg runtime.store.ModuleInst.memories functionMap
  dsimp only at functionMap_memories
  have functionSource : funcInst.module = seed.module := by
    simpa only [functionMap_module] using typeSource
  obtain ⟨tableStart, importedAddresses⟩ := maps.table_start cache
  have tableStartBound : funcInst.tables.len.val ≤ funcInst.module.module.env.table_types.val.length := by
    simpa only [TableTypeMap, alloc.vec.Vec.len_val, alloc.vec.Vec.length, functionMap_tables, typeMap_tables, functionMap_module, typeMap_module] using tableStart
  have tableIssued : ∀ addr ∈ funcInst.tables.val, addr.index.val < functions.tables.length := by
    simpa only [functionMap_tables, typeMap_tables, functionStore_tables, typeStore_tables] using importedAddresses
  have importedTyped : TableTypeMap functions (funcInst.module.module.env.table_types.val.take funcInst.tables.len.val) funcInst.tables.val := by
    have initial := maps.table_types
    have count := maps.tables.length_eq
    have sourcePrefix : seed.module.module.env.table_types.val.take seed.tables.val.length = importedTables seed.module.module.env.imports.val := by
      rw [cache.tables, ← count, List.take_left]
    simpa only [TableTypeMap, alloc.vec.Vec.len_val, alloc.vec.Vec.length, functionMap_tables, typeMap_tables,
      functionMap_module, typeMap_module, sourcePrefix, functionStore_tables, typeStore_tables] using initial
  have tableOwners : ∀ address ∈ funcInst.tables.val, address.store = functions.id := by
    have functionId : functions.id = before.id := by rw [functionStore, typeStore]
    simpa only [functionMap_tables, typeMap_tables, functionId] using maps.tables_owned
  have tableChecked  := table_allocated_loop memory allocator law view functions functions funcInst funcInst funcInst.tables.len
    tableStartBound rfl rfl (.refl _) functionBound functionAllocated tableIssued tableOwners (by simp) importedTyped
  have tablePost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ tableChecked tabled tableInst (.Ok ()) tableRun
  obtain ⟨tableStore, tableMap, tablePrefix, tableBound, tableAllocated, tableAddresses, finalTableOwners, tableCount, tableTypes⟩ := tablePost
  have tableStore_funcs := congrArg runtime.store.Store.funcs tableStore
  dsimp only at tableStore_funcs
  have tableStore_memories := congrArg runtime.store.Store.memories tableStore
  dsimp only at tableStore_memories
  have tableMap_module := by
    have h := congrArg runtime.store.ModuleInst.module tableMap; exact h
  dsimp only at tableMap_module
  have tableMap_funcs := congrArg runtime.store.ModuleInst.funcs tableMap
  dsimp only at tableMap_funcs
  have tableMap_memories := congrArg runtime.store.ModuleInst.memories tableMap
  dsimp only at tableMap_memories
  obtain ⟨memoryStart, importedMemories⟩ := maps.memory_start cache
  have memoryStartBound : tableInst.memories.len.val ≤ tableInst.module.module.env.mem_types.val.length := by
    simpa only [TableTypeMap, alloc.vec.Vec.len_val, alloc.vec.Vec.length, tableMap_memories, functionMap_memories, typeMap_memories, tableMap_module, functionMap_module, typeMap_module] using memoryStart
  have memoryIssued : ∀ addr ∈ tableInst.memories.val, addr.index.val < tabled.memories.length := by
    simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableStore_memories, functionStore_memories, typeStore_memories] using importedMemories
  have memoryOwners : ∀ address ∈ tableInst.memories.val, address.store = tabled.id := by
    have tableId : tabled.id = before.id := by rw [tableStore, functionStore, typeStore]
    simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableId] using maps.memories_owned
  have memoryChecked  := memory_allocated_loop memory allocator law view laws tabled tabled tableInst tableInst tableInst.memories.len
    memoryStartBound rfl rfl (.refl _) tableBound tableAllocated memoryIssued memoryOwners (by simp)
  have memoryPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ memoryChecked after inst (.Ok ()) memoryRun
  obtain ⟨memoryStore, memoryMap, memoryPrefix, memoryBound, memoryAllocated, memoryAddresses, finalMemoryOwners, memoryCount⟩ := memoryPost
  have tableSource : tableInst.module = funcInst.module := by
    have h := congrArg runtime.store.ModuleInst.module tableMap; exact h
  have memorySource : inst.module = tableInst.module := by
    have h := congrArg runtime.store.ModuleInst.module memoryMap; exact h
  have memoryTables : inst.tables = tableInst.tables := by
    have h := congrArg runtime.store.ModuleInst.tables memoryMap; exact h
  have retainedTables : after.tables = tabled.tables := by
    have h := congrArg runtime.store.Store.tables memoryStore; exact h
  refine ⟨?_, ?_, ?_, ?_, memoryAllocated⟩
  · simpa only [TableTypeMap, memorySource, tableSource, memoryTables, retainedTables] using tableTypes rfl
  · intro address member
    have old : address ∈ tableInst.tables.val := by simpa only [memoryTables] using member
    have memoryId : after.id = tabled.id := by rw [memoryStore]
    exact ⟨by simpa only [memoryId] using finalTableOwners address old,
      by simpa only [retainedTables] using tableAddresses address old⟩
  · intro address member
    exact ⟨finalMemoryOwners address member, memoryAddresses address member⟩
  · simpa only [memorySource] using memoryCount rfl

end Exec.Store
