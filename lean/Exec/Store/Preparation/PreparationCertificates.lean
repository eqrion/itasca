import Exec.Store.Preparation.PreparationResults
import Exec.Store.Invariant.FunctionPreparation

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Successful actual preparation constructs canonical type/function maps and
retains exact source indices/signatures for every new defined function. These
are the structural inputs to compiled-function coverage after publication. -/
theorem preparation_certificates {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (seed : runtime.store.ModuleInst)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (instanceIndex : Usize)
    (typed functions tabled after : runtime.store.Store M)
    (typeInst funcInst tableInst inst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst instanceIndex =
      .ok (typeParts functions (.Ok ()) funcInst))
    (tableRun : runtime.store.instantiate.Store.prepare_instance_loop5 memory allocator functions (.Ok ()) funcInst.tables.len funcInst =
      .ok (typeParts tabled (.Ok ()) tableInst))
    (memoryRun : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator tabled (.Ok ()) tableInst.memories.len tableInst =
      .ok (typeParts after (.Ok ()) inst)) :
    TypeEntries after seed.module.module.env.types.val inst.types.val ∧
    Interp.FunctionTable after inst (seed.module.module.env.func_types.val.map decodeFuncType) ∧
    StagedFunctionSignatures before after instanceIndex
      (seed.module.module.env.func_types.val.drop (importedFuncs seed.module.module.env.imports.val).length) := by
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
  have functionMap_module := congrArg runtime.store.ModuleInst.module functionMap
  dsimp only at functionMap_module
  have functionMap_tables := congrArg runtime.store.ModuleInst.tables functionMap
  dsimp only at functionMap_tables
  have functionMap_memories := congrArg runtime.store.ModuleInst.memories functionMap
  dsimp only at functionMap_memories
  have functionSource : funcInst.module = seed.module := by
    simpa only [functionMap_module] using typeSource
  obtain ⟨tableStart, importedTables⟩ := maps.table_start cache
  have tableStartBound : funcInst.tables.len.val ≤ funcInst.module.module.env.table_types.val.length := by
    simpa only [alloc.vec.Vec.len_val, functionMap_tables, typeMap_tables, functionMap_module, typeMap_module] using tableStart
  have tableIssued : ∀ addr ∈ funcInst.tables.val, addr.index.val < functions.tables.length := by
    simpa only [functionMap_tables, typeMap_tables, functionStore_tables, typeStore_tables] using importedTables
  have tableChecked := table_staging_loop memory allocator law functions functions funcInst funcInst funcInst.tables.len
    tableStartBound rfl rfl (.refl _) functionBound tableIssued (by simp)
  have tablePost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ tableChecked tabled tableInst (.Ok ()) tableRun
  obtain ⟨tableStore, tableMap, tablePrefix, tableBound, tableAddresses, tableCount⟩ := tablePost
  have tableStore_funcs := congrArg runtime.store.Store.funcs tableStore
  dsimp only at tableStore_funcs
  have tableStore_memories := congrArg runtime.store.Store.memories tableStore
  dsimp only at tableStore_memories
  have tableMap_module := congrArg runtime.store.ModuleInst.module tableMap
  dsimp only at tableMap_module
  have tableMap_funcs := congrArg runtime.store.ModuleInst.funcs tableMap
  dsimp only at tableMap_funcs
  have tableMap_memories := congrArg runtime.store.ModuleInst.memories tableMap
  dsimp only at tableMap_memories
  obtain ⟨memoryStart, importedMemories⟩ := maps.memory_start cache
  have memoryStartBound : tableInst.memories.len.val ≤ tableInst.module.module.env.mem_types.val.length := by
    simpa only [alloc.vec.Vec.len_val, tableMap_memories, functionMap_memories, typeMap_memories, tableMap_module, functionMap_module, typeMap_module] using memoryStart
  have memoryIssued : ∀ addr ∈ tableInst.memories.val, addr.index.val < tabled.memories.length := by
    simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableStore_memories, functionStore_memories, typeStore_memories] using importedMemories
  have memoryChecked := memory_staging_loop memory allocator law view laws tabled tabled tableInst tableInst tableInst.memories.len
    memoryStartBound rfl rfl (.refl _) tableBound memoryIssued (by simp)
  have memoryPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ memoryChecked after inst (.Ok ()) memoryRun
  obtain ⟨memoryStore, memoryMap, memoryPrefix, memoryBound, memoryAddresses, memoryCount⟩ := memoryPost
  have memoryStore_funcs := congrArg runtime.store.Store.funcs memoryStore
  dsimp only at memoryStore_funcs
  have memoryMap_funcs := congrArg runtime.store.ModuleInst.funcs memoryMap
  dsimp only at memoryMap_funcs
  have functionMap_types := congrArg runtime.store.ModuleInst.types functionMap
  dsimp only at functionMap_types
  have tableMap_types := congrArg runtime.store.ModuleInst.types tableMap
  dsimp only at tableMap_types
  have memoryMap_types := congrArg runtime.store.ModuleInst.types memoryMap
  dsimp only at memoryMap_types
  have finalEntries := (typeEntries rfl).extend (functionPrefix.trans (tablePrefix.trans memoryPrefix))
  have finalTable := function_table_prefix (tablePrefix.trans memoryPrefix) (functionTable rfl)
  have functionsSame : after.funcs = functions.funcs := memoryStore_funcs.trans tableStore_funcs
  have stagedFinal := (staged.extend (tablePrefix.trans memoryPrefix) functionsSame).rebase typeStore_funcs
  refine ⟨?_, ?_, ?_⟩
  · simpa only [memoryMap_types, tableMap_types, functionMap_types] using finalEntries
  · have rebound := function_table_instance (memoryMap_funcs.trans tableMap_funcs) finalTable
    simpa only [typeSource] using rebound
  · simpa only [typeSource] using stagedFinal

end Itasca.Runtime.Store
