import Exec.Store.Preparation.PreparationResults

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Compose the four actual successful preparation-loop equations. The loop
proofs separately establish totality, including each failure branch. This
success inversion constructs the initializer context required immediately
before publication of the provisional instance. -/
theorem preparation_success {M A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
    inst.module = seed.module ∧ after.globals = before.globals ∧
    after.instances = before.instances ∧ after.elems = before.elems ∧ after.datas = before.datas ∧
    inst.globals = seed.globals ∧
    inst.elems = seed.elems ∧ inst.datas = seed.datas ∧
    InitializerBindings after inst ∧ InitializerImports after inst ∧ InitializerSegmentBindings after inst := by
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
  have typeSource : typeInst.module = seed.module := by
    have h := congrArg runtime.store.ModuleInst.module typeMap
    exact h
  have typeFuncs : typeInst.funcs = seed.funcs := by
    have h := congrArg runtime.store.ModuleInst.funcs typeMap
    exact h
  have typesComplete : typeInst.types.length = seed.module.module.env.types.length :=
    (typeEntries rfl).length_eq.symm
  have sourceIndices := cache_defined_type_bounds cache typeInst.types typesComplete
  have preparedIndices : ∀ idx ∈ typeInst.module.module.env.func_type_indices.val,
      idx.val < typeInst.types.length := by simpa only [typeSource] using sourceIndices
  have importedIssued := (maps.bindings shape).funcs
  have typedIssued : ∀ addr ∈ typeInst.funcs.val, addr.index.val < typed.funcs.length := by
    simpa only [typeFuncs, typeStore_funcs] using importedIssued
  have functionCapacity : typeInst.funcs.length + typeInst.module.module.env.func_type_indices.val.length ≤ Usize.max := by
    simpa only [typeFuncs, typeSource] using maps.function_capacity cache
  have functionChecked := function_staging_loop memory allocator law typed typed typeInst typeInst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) typeBound preparedIndices typedIssued (by simp) functionCapacity
  have functionPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ functionChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨functionStore, functionMap, functionPrefix, functionBound, functionIssued, functionCount⟩ := functionPost
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
  have memoryStore_tables := congrArg runtime.store.Store.tables memoryStore
  dsimp only at memoryStore_tables
  have memoryStore_globals := congrArg runtime.store.Store.globals memoryStore
  dsimp only at memoryStore_globals
  have memoryStore_instances := congrArg runtime.store.Store.instances memoryStore
  dsimp only at memoryStore_instances
  have memoryStore_elems := congrArg runtime.store.Store.elems memoryStore
  dsimp only at memoryStore_elems
  have memoryStore_datas := congrArg runtime.store.Store.datas memoryStore
  dsimp only at memoryStore_datas
  have memoryMap_module := congrArg runtime.store.ModuleInst.module memoryMap
  dsimp only at memoryMap_module
  have memoryMap_funcs := congrArg runtime.store.ModuleInst.funcs memoryMap
  dsimp only at memoryMap_funcs
  have memoryMap_tables := congrArg runtime.store.ModuleInst.tables memoryMap
  dsimp only at memoryMap_tables
  have memoryMap_globals := congrArg runtime.store.ModuleInst.globals memoryMap
  dsimp only at memoryMap_globals
  have memoryMap_elements := congrArg runtime.store.ModuleInst.elems memoryMap
  dsimp only at memoryMap_elements
  have memoryMap_data := congrArg runtime.store.ModuleInst.datas memoryMap
  dsimp only at memoryMap_data
  have retained := ((typePrefix.trans functionPrefix).trans tablePrefix).trans memoryPrefix
  have source : inst.module = seed.module := by simpa only [memoryMap_module, tableMap_module] using functionSource
  have globals : after.globals = before.globals := by
    simp only [memoryStore_globals, tableStore_globals, functionStore_globals, typeStore_globals]
  have globalMap : inst.globals = seed.globals := by simp only [memoryMap_globals, tableMap_globals, functionMap_globals, typeMap_globals]
  have functionLength : inst.funcs.val.length = seed.module.module.env.func_types.val.length := by
    have complete := functionCount rfl
    have counts := complete_function_count cache seed.funcs.length funcInst.funcs.length
      maps.funcs.length_eq.symm (by simpa only [typeFuncs, typeSource] using complete)
    simpa only [memoryMap_funcs, tableMap_funcs] using counts
  have functionAddresses : ∀ addr ∈ inst.funcs.val, addr.index.val < after.funcs.length := by
    simpa only [memoryMap_funcs, tableMap_funcs, memoryStore_funcs, tableStore_funcs] using functionIssued
  have tableLength : inst.tables.val.length = seed.module.module.env.table_types.val.length := by
    simpa only [memoryMap_tables, functionSource] using tableCount rfl
  have tableAddressesFinal : ∀ addr ∈ inst.tables.val, addr.index.val < after.tables.length := by
    simpa only [memoryMap_tables, memoryStore_tables] using tableAddresses
  have memoryLength : inst.memories.val.length = seed.module.module.env.mem_types.val.length := by
    simpa only [tableMap_module, functionSource] using memoryCount rfl
  have contexts := prepared_initializer_bindings view before after seed inst shape maps cache retained source globalMap globals
    functionLength functionAddresses tableLength memoryLength tableAddressesFinal memoryAddresses
  refine ⟨retained, memoryBound, source, globals, ?_, ?_, ?_, globalMap, ?_, ?_, contexts⟩
  · simp only [memoryStore_instances, tableStore_instances, functionStore_instances, typeStore_instances]
  · simp only [memoryStore_elems, tableStore_elems, functionStore_elems, typeStore_elems]
  · simp only [memoryStore_datas, tableStore_datas, functionStore_datas, typeStore_datas]
  · simp only [memoryMap_elements, tableMap_elements, functionMap_elements, typeMap_elements]
  · simp only [memoryMap_data, tableMap_data, functionMap_data, typeMap_data]

end Exec.Store
