import Exec.Store.Preparation.PreparationResults
import Exec.Store.Invariant.FunctionPayloadLoop
import Exec.Store.Invariant.FunctionOrderLoop
namespace Exec.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

theorem preparation_function_payload {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (before : runtime.store.Store M) (seed : runtime.store.ModuleInst)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (instanceIndex : Usize) (typed functions : runtime.store.Store M)
    (typeInst funcInst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.instantiate_inner_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.instantiate_inner_loop4 memory allocator typed (.Ok ()) 0#usize typeInst instanceIndex =
      .ok (typeParts functions (.Ok ()) funcInst)) :
    typed.funcs = before.funcs ∧ typeInst.module = seed.module ∧ typeInst.funcs = seed.funcs ∧
    TypeEntries typed seed.module.module.env.types.val typeInst.types.val ∧
    FunctionPayload typed functions typeInst instanceIndex seed.module.module.env.func_type_indices.val.length ∧
    functions.funcs.length = before.funcs.length + seed.module.module.env.func_type_indices.val.length ∧
    funcInst.funcs.val.map (fun a => a.index.val) = seed.funcs.val.map (fun a => a.index.val) ++
      List.range' before.funcs.length seed.module.module.env.func_type_indices.val.length := by
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
  have payloadChecked := function_payload_loop memory allocator law typed typed typeInst typeInst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) typeBound preparedIndices typedIssued (by simp) functionCapacity
    (.initial typed typeInst instanceIndex)
  have payloadPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ payloadChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨_, _, _, _, _, completed⟩ := payloadPost
  obtain ⟨count, payload⟩ := completed rfl
  have orderChecked := function_order_loop memory allocator law typed typed typeInst typeInst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) typeBound preparedIndices typedIssued (by simp) functionCapacity
    typed.funcs.length (typeInst.funcs.val.map fun a => a.index.val) (.refl _ _)
  have orderPost := preparation_result typeParts (fun a b s t i j h => (typeParts_inj a b s t i j).mp h)
    _ _ orderChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨_, _, _, _, ordered, _, _⟩ := orderPost
  obtain ⟨storeCount, addressValues⟩ := ordered.complete (by simpa only [List.length_map] using count)
  refine ⟨typeStore_funcs, typeSource, typeFuncs, typeEntries rfl, ?_, ?_, ?_⟩
  · simpa only [typeSource] using payload
  · simpa only [typeStore_funcs, typeSource] using storeCount
  · simpa only [typeStore_funcs, typeSource, typeFuncs] using addressValues
end Exec.Store
