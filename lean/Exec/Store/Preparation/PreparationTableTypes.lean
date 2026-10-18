import Exec.Store.Preparation.PreparationResults
import Exec.Store.Invariant.FunctionPreparation
import Exec.Store.Api.TableTypeLoop

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Successful actual preparation preserves imported table types and constructs
the exact source-to-raw type map for every newly allocated table. -/
theorem preparation_table_types {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.Instance)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (instanceIndex : Usize)
    (typed functions tabled after : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.Instance)
    (typeRun : runtime.store.instantiate.Store.instantiate_inner_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.instantiate_inner_loop4 memory allocator typed (.Ok ()) 0#usize typeInst instanceIndex =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.instantiate_inner_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.instantiate_inner_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts after (.Ok ()) inst)) :
    TableTypeMap after inst.module.module.env.table_types.val inst.tables.val := by
  have objectBound : objectCount before ≤ Usize.max := by
    have bound := shape.objectLimit
    unfold objectCount
    scalar_tac
  have emptyTypes : TypeEntries before (seed.module.module.env.types.val.take 0) seed.types.val := by
    simp [TypeEntries, maps.types]
  have typeChecked := type_staging_loop memory allocator law before before seed seed 0#usize
    (by simp) rfl rfl (.refl _) objectBound emptyTypes
  have typePost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ typeChecked typed typeInst (.Ok ()) typeRun
  obtain ⟨typeStore, typeMap, typePrefix, typeBound, typeEntries⟩ := typePost
  have typeStore_funcs := congrArg runtime.store.Store.funcs typeStore
  dsimp only at typeStore_funcs
  have typeStore_tables := congrArg runtime.store.Store.tables typeStore
  dsimp only at typeStore_tables
  have typeStore_memories := congrArg runtime.store.Store.memories typeStore
  dsimp only at typeStore_memories
  have typeMap_module := congrArg runtime.store.Instance.module typeMap
  dsimp only at typeMap_module
  have typeMap_tables := congrArg runtime.store.Instance.tables typeMap
  dsimp only at typeMap_tables
  have typeMap_memories := congrArg runtime.store.Instance.memories typeMap
  dsimp only at typeMap_memories
  have typeSource : typeInst.module = seed.module := by
    have h := congrArg runtime.store.Instance.module typeMap
    exact h
  have typeFuncs : typeInst.funcs = seed.funcs := by
    have h := congrArg runtime.store.Instance.funcs typeMap
    exact h
  have typeTable : Interp.FunctionTable typed typeInst
      ((typeInst.module.module.env.func_types.val.take (importedFuncs typeInst.module.module.env.imports.val).length).map decodeFuncType) := by
    have linkedTable := function_table_instance typeFuncs (function_table_prefix typePrefix (maps.function_table cache))
    simpa only [typeSource] using linkedTable
  have typeCache : Cache typeInst.module.module.env tables memories := by simpa only [typeSource] using cache
  have mappedTypes : TypeEntries typed typeInst.module.module.env.types.val typeInst.types.val := by
    simpa only [typeSource] using typeEntries rfl
  have functionChecked := prepare_function_signatures memory allocator law typed typeInst instanceIndex typeCache
    typeBound mappedTypes typeTable
  have functionPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ functionChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨functionStore, functionMap, functionPrefix, functionBound, functionTable, staged⟩ := functionPost
  have functionIssued := function_table_issued (functionTable rfl)
  have functionStore_tables := congrArg runtime.store.Store.tables functionStore
  dsimp only at functionStore_tables
  have functionStore_memories := congrArg runtime.store.Store.memories functionStore
  dsimp only at functionStore_memories
  have functionMap_module := congrArg runtime.store.Instance.module functionMap
  dsimp only at functionMap_module
  have functionMap_tables := congrArg runtime.store.Instance.tables functionMap
  dsimp only at functionMap_tables
  have functionMap_memories := congrArg runtime.store.Instance.memories functionMap
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
  have tableChecked := table_type_staging_loop memory allocator law functions functions funcInst funcInst funcInst.tables.len
    tableStartBound rfl rfl (.refl _) functionBound tableIssued (by simp) importedTyped
  have tablePost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ tableChecked tabled tableInst (.Ok ()) tableRun
  obtain ⟨tableStore, tableMap, tablePrefix, tableBound, tableAddresses, tableCount, tableTypes⟩ := tablePost
  have tableStore_funcs := congrArg runtime.store.Store.funcs tableStore
  dsimp only at tableStore_funcs
  have tableStore_memories := congrArg runtime.store.Store.memories tableStore
  dsimp only at tableStore_memories
  have tableMap_module := by
    have h := congrArg runtime.store.Instance.module tableMap; exact h
  dsimp only at tableMap_module
  have tableMap_funcs := congrArg runtime.store.Instance.funcs tableMap
  dsimp only at tableMap_funcs
  have tableMap_memories := congrArg runtime.store.Instance.memories tableMap
  dsimp only at tableMap_memories
  obtain ⟨memoryStart, importedMemories⟩ := maps.memory_start cache
  have memoryStartBound : tableInst.memories.len.val ≤ tableInst.module.module.env.mem_types.val.length := by
    simpa only [TableTypeMap, alloc.vec.Vec.len_val, alloc.vec.Vec.length, tableMap_memories, functionMap_memories, typeMap_memories, tableMap_module, functionMap_module, typeMap_module] using memoryStart
  have memoryIssued : ∀ addr ∈ tableInst.memories.val, addr.index.val < tabled.memories.length := by
    simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableStore_memories, functionStore_memories, typeStore_memories] using importedMemories
  have memoryChecked := memory_staging_loop memory allocator law view laws tabled tabled tableInst tableInst tableInst.memories.len
    memoryStartBound rfl rfl (.refl _) tableBound memoryIssued (by simp)
  have memoryPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ memoryChecked after inst (.Ok ()) memoryRun
  obtain ⟨memoryStore, memoryMap, memoryPrefix, memoryBound, memoryAddresses, memoryCount⟩ := memoryPost
  have tableSource : tableInst.module = funcInst.module := by
    have h := congrArg runtime.store.Instance.module tableMap; exact h
  have memorySource : inst.module = tableInst.module := by
    have h := congrArg runtime.store.Instance.module memoryMap; exact h
  have memoryTables : inst.tables = tableInst.tables := by
    have h := congrArg runtime.store.Instance.tables memoryMap; exact h
  have retainedTables : after.tables = tabled.tables := by
    have h := congrArg runtime.store.Store.tables memoryStore; exact h
  simpa only [TableTypeMap, memorySource, tableSource, memoryTables, retainedTables] using tableTypes rfl

end Exec.Store
