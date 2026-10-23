import Exec.Store.Preparation.PreparationResults
import Exec.Store.Invariant.FunctionPreparation
import Exec.Store.Api.TableBindingLoop
import Exec.Store.Api.MemoryBindingLoop
import Exec.Store.Api.TableAllocationLoop
import Exec.Store.Api.MemoryAllocationLoop

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Successful preparation appends exactly the source-defined null tables and
zero memories, with consecutive fresh addresses in the instance maps. -/
theorem preparation_table_memory_allocations_metadata {M A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    after.tables.val.map decodeTable = before.tables.val.map decodeTable ++
      tables.map (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty)) ∧
    after.memories.val.map (decodeMemory view) = before.memories.val.map (decodeMemory view) ++
      memories.map (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty)) ∧
    inst.tables.val.map (fun address => address.index.val) =
      seed.tables.val.map (fun address => address.index.val) ++ List.range' before.tables.length tables.length ∧
    inst.memories.val.map (fun address => address.index.val) =
      seed.memories.val.map (fun address => address.index.val) ++ List.range' before.memories.length memories.length ∧
    after.tables.length = before.tables.length + tables.length ∧
    after.memories.length = before.memories.length + memories.length ∧
    after.funcs = functions.funcs ∧ after.types = typed.types ∧
    inst.funcs = funcInst.funcs ∧ inst.types = typeInst.types ∧ inst.module = seed.module := by
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
  obtain ⟨tableStart, importedAddresses⟩ := maps.table_start cache
  have tableStartBound : funcInst.tables.len.val ≤ funcInst.module.module.env.table_types.val.length := by
    simpa only [TableBindings, alloc.vec.Vec.len_val, alloc.vec.Vec.length, functionMap_tables, typeMap_tables, functionMap_module, typeMap_module] using tableStart
  have tableIssued : ∀ addr ∈ funcInst.tables.val, addr.index.val < functions.tables.length := by
    simpa only [functionMap_tables, typeMap_tables, functionStore_tables, typeStore_tables] using importedAddresses
  have importedTyped : TableBindings functions (funcInst.module.module.env.table_types.val.take funcInst.tables.len.val) funcInst.tables.val := by
    have initial := TableBindings.prefix maps.tables (typePrefix.trans functionPrefix).identity (typePrefix.trans functionPrefix).tables
    have count := maps.tables.length_eq
    have sourcePrefix : seed.module.module.env.table_types.val.take seed.tables.val.length = importedTables seed.module.module.env.imports.val := by
      rw [cache.tables, ← count, List.take_left]
    simpa only [TableBindings, alloc.vec.Vec.len_val, alloc.vec.Vec.length, functionMap_tables, typeMap_tables,
      functionMap_module, typeMap_module, sourcePrefix, functionStore_tables, typeStore_tables] using initial
  have tableChecked := table_binding_staging_loop memory allocator law functions functions funcInst funcInst funcInst.tables.len
    tableStartBound rfl rfl (.refl _) functionBound tableIssued (by simp) importedTyped
  have tablePost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ tableChecked tabled tableInst (.Ok ()) tableRun
  obtain ⟨tableStore, tableMap, tablePrefix, tableBound, tableAddresses, tableCount, tableTypes⟩ := tablePost
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
    simpa only [TableBindings, alloc.vec.Vec.len_val, alloc.vec.Vec.length, tableMap_memories, functionMap_memories, typeMap_memories, tableMap_module, functionMap_module, typeMap_module] using memoryStart
  have memoryIssued : ∀ addr ∈ tableInst.memories.val, addr.index.val < tabled.memories.length := by
    simpa only [tableMap_memories, functionMap_memories, typeMap_memories, tableStore_memories, functionStore_memories, typeStore_memories] using importedMemories
  have importedMemoryBindings : MemoryBindings view tabled (tableInst.module.module.env.mem_types.val.take tableInst.memories.len.val) tableInst.memories.val := by
    have retained := (typePrefix.trans functionPrefix).trans tablePrefix
    have initial := MemoryBindings.prefix maps.memories retained.identity retained.memories
    have count := maps.memories.length_eq
    have sourcePrefix : seed.module.module.env.mem_types.val.take seed.memories.val.length = importedMems seed.module.module.env.imports.val := by
      rw [cache.memories, ← count, List.take_left]
    simpa only [alloc.vec.Vec.len_val, alloc.vec.Vec.length, tableMap_memories, functionMap_memories, typeMap_memories,
      tableMap_module, functionMap_module, typeMap_module, sourcePrefix] using initial
  have memoryChecked := memory_binding_staging_loop memory allocator law view laws tabled tabled tableInst tableInst tableInst.memories.len
    memoryStartBound rfl rfl (.refl _) tableBound memoryIssued (by simp) importedMemoryBindings
  have memoryPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ memoryChecked after inst (.Ok ()) memoryRun
  obtain ⟨memoryStore, memoryMap, memoryPrefix, memoryBound, memoryAddresses, memoryCount, memoryBindings⟩ := memoryPost
  have tableSource : tableInst.module = funcInst.module := by
    have h := congrArg runtime.store.ModuleInst.module tableMap; exact h
  have memorySource : inst.module = tableInst.module := by
    have h := congrArg runtime.store.ModuleInst.module memoryMap; exact h
  have memoryTables : inst.tables = tableInst.tables := by
    have h := congrArg runtime.store.ModuleInst.tables memoryMap; exact h
  have retainedTables : after.tables = tabled.tables := by
    have h := congrArg runtime.store.Store.tables memoryStore; exact h
  have allocatedTables := table_allocation_success memory allocator law functions tabled funcInst tableInst
    funcInst.tables.len tableStartBound functionBound tableIssued (by simp) tableRun
  have allocatedMemories := memory_allocation_success memory allocator law view laws tabled after tableInst inst
    tableInst.memories.len memoryStartBound tableBound memoryIssued (by simp) memoryRun
  have definedTables : funcInst.module.module.env.table_types.val.drop funcInst.tables.len.val = tables := by
    simp only [functionSource, alloc.vec.Vec.len_val, functionMap_tables, typeMap_tables,
      cache.tables, ← maps.tables.length_eq, List.drop_left]
  have definedMemories : tableInst.module.module.env.mem_types.val.drop tableInst.memories.len.val = memories := by
    simp only [tableMap_module, functionSource, alloc.vec.Vec.len_val, tableMap_memories,
      functionMap_memories, typeMap_memories, cache.memories, ← maps.memories.length_eq, List.drop_left]
  have tableLength : funcInst.module.module.env.table_types.val.length - funcInst.tables.len.val = tables.length := by
    rw [← List.length_drop, definedTables]
  have memoryLength : tableInst.module.module.env.mem_types.val.length - tableInst.memories.len.val = memories.length := by
    rw [← List.length_drop, definedMemories]
  rw [definedTables, tableLength] at allocatedTables
  rw [definedMemories, memoryLength] at allocatedMemories
  simp only [functionStore_tables, typeStore_tables,
    functionMap_tables, typeMap_tables] at allocatedTables
  simp only [tableStore_memories, functionStore_memories,
    typeStore_memories, tableMap_memories, functionMap_memories, typeMap_memories] at allocatedMemories
  refine ⟨by simpa only [retainedTables] using allocatedTables.1, allocatedMemories.1,
    by simpa only [memoryTables] using allocatedTables.2.2, allocatedMemories.2.2,
    by simpa only [retainedTables] using allocatedTables.2.1, allocatedMemories.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg runtime.store.Store.funcs memoryStore).trans tableStore_funcs
  · have a : after.types = tabled.types := by
      have h := congrArg runtime.store.Store.types memoryStore
      exact h
    have b : tabled.types = functions.types := by
      have h := congrArg runtime.store.Store.types tableStore
      exact h
    have c : functions.types = typed.types := by
      have h := congrArg runtime.store.Store.types functionStore
      exact h
    exact a.trans (b.trans c)
  · exact (congrArg runtime.store.ModuleInst.funcs memoryMap).trans tableMap_funcs
  · have a : inst.types = tableInst.types := by
      have h := congrArg runtime.store.ModuleInst.types memoryMap
      exact h
    have b : tableInst.types = funcInst.types := by
      have h := congrArg runtime.store.ModuleInst.types tableMap
      exact h
    have c : funcInst.types = typeInst.types := by
      have h := congrArg runtime.store.ModuleInst.types functionMap
      exact h
    exact a.trans (b.trans c)
  · exact memorySource.trans (tableSource.trans functionSource)

/-- Successful preparation appends exactly the source-defined null tables and
zero memories, with consecutive fresh addresses in the instance maps. -/
theorem preparation_table_memory_allocations {M A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    after.tables.val.map decodeTable = before.tables.val.map decodeTable ++
      tables.map (fun ty => Spec.allocationTable (Itasca.EnvTranslation.tableType ty)) ∧
    after.memories.val.map (decodeMemory view) = before.memories.val.map (decodeMemory view) ++
      memories.map (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty)) ∧
    inst.tables.val.map (fun address => address.index.val) =
      seed.tables.val.map (fun address => address.index.val) ++ List.range' before.tables.length tables.length ∧
    inst.memories.val.map (fun address => address.index.val) =
      seed.memories.val.map (fun address => address.index.val) ++ List.range' before.memories.length memories.length ∧
    after.tables.length = before.tables.length + tables.length ∧
    after.memories.length = before.memories.length + memories.length := by
  obtain ⟨tables, memories, tableMap, memoryMap, tableCount, memoryCount, _⟩ :=
    preparation_table_memory_allocations_metadata memory allocator law view laws before seed shape maps cache instanceIndex typed functions tabled after typeInst funcInst tableInst inst typeRun functionRun tableRun memoryRun
  exact ⟨tables, memories, tableMap, memoryMap, tableCount, memoryCount⟩
end Exec.Store
