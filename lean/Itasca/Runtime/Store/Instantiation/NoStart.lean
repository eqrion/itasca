import Itasca.Generated.Funs
import Itasca.Runtime.Store.Preparation.PreparationErrorLoops
import Itasca.Runtime.Store.Invariant.FunctionAndTypeStagingCauses
import Itasca.Runtime.Store.Instantiation.Linked
import Itasca.Runtime.Store.Instantiation.TailCommit
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Linking.LinkLoop
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Store.Api.AllocationLoops
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Store.Initialization.SegmentLoops
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Invariant.SourceAllocationLists
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions
import Itasca.Runtime.Store.Api.ObjectStaging
import Itasca.Runtime.Equations.Interp
import Itasca.Runtime.Store.Initialization.SegmentInitializePreservation

/-!
Proofs for Runtime / Store / Instantiation.

This module collects PreparationFunctionPayload, NoStart.
Each section documents its contracts and consumers.
-/

/-! ## PreparationFunctionPayload -/

section

open Itasca.Representation

/-!
# Prepared function payloads

Preparation retains the function payload established during function staging. The instantiation join uses this evidence alongside later table and memory allocations.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Module.Environment

theorem preparation_function_payload {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (before : runtime.store.Store M) (seed : runtime.store.ModuleInst)
    (shape : Shape view before)
    (maps : LinkedMaps view before seed.module seed.module.module.env.imports.val seed)
    {tables memories} (cache : Cache seed.module.module.env tables memories)
    (instanceIndex : Usize) (typed functions : runtime.store.Store M)
    (typeInst funcInst : runtime.store.ModuleInst)
    (typeRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator before (.Ok ()) 0#usize seed =
      .ok (typeParts typed (.Ok ()) typeInst))
    (functionRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator typed (.Ok ()) 0#usize typeInst instanceIndex =
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
  have typePost := preparation_result typeParts (fun a b s t i j h => (type_parts_inj a b s t i j).mp h)
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
  have payloadPost := preparation_result typeParts (fun a b s t i j h => (type_parts_inj a b s t i j).mp h)
    _ _ payloadChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨_, _, _, _, _, completed⟩ := payloadPost
  obtain ⟨count, payload⟩ := completed rfl
  have orderChecked := function_order_loop memory allocator law typed typed typeInst typeInst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) typeBound preparedIndices typedIssued (by simp) functionCapacity
    typed.funcs.length (typeInst.funcs.val.map fun a => a.index.val) (.refl _ _)
  have orderPost := preparation_result typeParts (fun a b s t i j h => (type_parts_inj a b s t i j).mp h)
    _ _ orderChecked functions funcInst (.Ok ()) functionRun
  obtain ⟨_, _, _, _, ordered, _, _⟩ := orderPost
  obtain ⟨storeCount, addressValues⟩ := ordered.complete (by simpa only [List.length_map] using count)
  refine ⟨typeStore_funcs, typeSource, typeFuncs, typeEntries rfl, ?_, ?_, ?_⟩
  · simpa only [typeSource] using payload
  · simpa only [typeStore_funcs, typeSource] using storeCount
  · simpa only [typeStore_funcs, typeSource, typeFuncs] using addressValues
end Itasca.Store

end

/-! ## NoStart -/

section

/-!
Proofs for Runtime / Store / Instantiation.

This module collects Precommit, NoStart.
Each section documents its contracts and consumers.
-/

/-! ## Precommit -/

section

open Itasca.Representation

/-!
Pre-publication instantiation, rollback and resource causes. Publication boundaries and the resolved, unexecuted start function remain explicit.
-/

/-! ## Instantiate Precommit -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- A normally returning precommit rejection of an actually compiled module
has one of the documented API or resource causes. Traps cannot originate
before publication. Foreign handles are admitted
by ExternalIssued and retain their explicit WrongStore outcome. -/
theorem instantiate_compiled_precommit_origins {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (error : runtime.ExecError) (staged : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
      .ok (.Err error, staged, host, false)) :
    PrecommitError error ∧ host = platform ∧ StagedPrefix before staged ∧
      PrecommitOrigins memory view before staged module imports error := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have actualValid : Itasca.Module.Environment.Valid module.module.env := by
    exact valid
  have decomposition := instantiate_inner_classified_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache actualValid dataValid certificates.2.2 handles _ run
  rcases decomposition with ⟨rejected, after, outcome, retained, cause, origins⟩ |
      ⟨ready, inst, readyShape, found, source, initializers, types, counts, code, trace, tail⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at outcome
    obtain ⟨rfl, rfl, rfl, _⟩ := outcome
    exact ⟨cause, rfl, retained, origins⟩
  · have committed := instantiate_tail_committed_result memory hooks floats allocator ⟨before.id, before.instances.len⟩
      ready platform _ tail
    contradiction

end Itasca.Store

end

/-! ## Instantiate Precommit Resources -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- A normally returning precommit rejection of an actually compiled module
has one of the documented API or resource causes. Traps cannot originate
before publication. Foreign handles are admitted
by ExternalIssued and retain their explicit WrongStore outcome. -/
theorem instantiate_compiled_precommit_resource_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (error : runtime.ExecError) (staged : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
      .ok (.Err error, staged, host, false)) :
    host = platform ∧ StagedPrefix before staged ∧
      PrecommitResourceEvidence memory hooks floats allocator before module imports platform error := by
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have actualValid : Itasca.Module.Environment.Valid module.module.env := by
    exact valid
  have decomposition := instantiate_inner_resource_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache actualValid dataValid certificates.2.2 handles _ run
  rcases decomposition with ⟨rejected, after, outcome, retained, causes⟩ |
      ⟨ready, inst, readyShape, found, source, initializers, types, counts, code, trace, tail⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at outcome
    obtain ⟨rfl, rfl, rfl, _⟩ := outcome
    exact ⟨rfl, retained, causes⟩
  · have committed := instantiate_tail_committed_result memory hooks floats allocator ⟨before.id, before.instances.len⟩
      ready platform _ tail
    contradiction

end Itasca.Store

end

end

/-! ## NoStart -/

section

open Itasca.Representation

/-!
# No Start

Prepared object maps and payloads construct source allocation and module instantiation. Export bounds and start-handle preparation stop before start-function execution.
-/

/-! ## PreparedSourceInstantiation -/

section

/-!
Source instantiation from the prepared concrete allocation. Function/global/segment payloads and external maps establish the source allocation step, then the prepared initialization composes it into source instantiation without executing start code.
-/

/-! ## Prepared External Maps -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Module.Environment

theorem LinkedPreparedRun.external_maps {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {imports : Slice runtime.Extern}
    {platform : P} {ready : runtime.store.Store M}
    (trace : LinkedPreparedRun memory hooks floats allocator view before module imports platform ready)
    (laws : Platform.MemoryLaws memory view) (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ExternalMaps imports.val trace.seed := by
  have maps : LinkedMaps view before module (module.module.env.imports.val.take 0) (emptyInstance module) := by
    simpa only [List.take_zero, emptyInstance] using linked_maps_empty view before (emptyInstance module)
      rfl rfl rfl rfl rfl rfl rfl
  have emptyMaps : ExternalMaps (imports.val.take 0) (emptyInstance module) := by
    constructor <;> simp [emptyInstance, externalFunctions, externalTables, externalMemories, externalGlobals]
  have checked := link_external_maps_loop memory view laws before shape module imports trace.importsLength
    handles cache (emptyInstance module) 0#usize (by simp) maps emptyMaps
  rw [trace.linkRun] at checked
  simp only [WP.spec_ok] at checked
  exact (checked.2.2 True.intro).2

theorem ExternalMaps.source (externals : List runtime.Extern) (inst : runtime.store.ModuleInst)
    (maps : ExternalMaps externals inst) :
    fun_funcs (externals.map decodeExternal) (inst.funcs.val.map fun a => a.index.val) ∧
    fun_globals (externals.map decodeExternal) (inst.globals.val.map fun a => a.index.val) ∧
    fun_tables (externals.map decodeExternal) (inst.tables.val.map fun a => a.index.val) ∧
    fun_mems (externals.map decodeExternal) (inst.memories.val.map fun a => a.index.val) := by
  rw [maps.funcs, maps.globals, maps.tables, maps.memories]
  exact ⟨external_functions externals, external_globals externals, external_tables externals,
    external_memories externals⟩
end Itasca.Store

end

/-! ## Prepared Function Payload -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Module.Environment

theorem PreparedRun.function_payload {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (law : Platform.AllocCorrect allocator) (shape : Shape view before)
    {tables memories} (cache : Cache module.module.env tables memories) :
    trace.typed.funcs = before.funcs ∧ trace.typeInst.module = module ∧ trace.typeInst.funcs = trace.seed.funcs ∧
    TypeEntries trace.typed module.module.env.types.val trace.typeInst.types.val ∧
    FunctionPayload trace.typed trace.functions trace.typeInst before.instances.len module.module.env.func_type_indices.val.length ∧
    trace.functions.funcs.length = before.funcs.length + module.module.env.func_type_indices.val.length ∧
    trace.funcInst.funcs.val.map (fun a => a.index.val) = trace.seed.funcs.val.map (fun a => a.index.val) ++
      List.range' before.funcs.length module.module.env.func_type_indices.val.length := by
  have result := preparation_function_payload memory allocator law view before trace.seed shape trace.maps
    (by simpa only [trace.source] using cache) before.instances.len trace.typed trace.functions trace.typeInst trace.funcInst
    trace.typeRun trace.functionRun
  simpa only [trace.source] using result
end Itasca.Store

end

/-! ## Prepared Global Source -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Module.Environment

/-- The exact successful preparation trace computes all global values required
by generated module allocation, in the original source store and initial frame. -/
theorem PreparedRun.global_source_context {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (initialModule : moduleinst)
    (functionMap : initialModule.FUNCS = trace.inst.funcs.val.map (fun address => address.index.val))
    (globalMap : initialModule.GLOBALS = trace.seed.globals.val.map (fun address => address.index.val))
    (storeWf : wf_store (decodeStore view code before))
    (frameWf : wf_frame ⟨[], initialModule⟩) :
    ∃ next, trace.globalStore.instances.val[before.instances.len.val]? = some next ∧
      next.module = module ∧
      InitializerFunctionMetadata {trace.prepared with instances := trace.publishedInstances} trace.inst trace.globalStore next ∧
      InitializerBindings trace.globalStore next ∧
      InitializerImports trace.globalStore next ∧ InitializerSegmentBindings trace.globalStore next ∧
      InitializerSourceContext (decodeStore view code before) initialModule trace.globalStore next ∧
      StagedPrefix before trace.globalStore ∧ objectCount trace.globalStore ≤ Usize.max ∧
      SegmentAccounting trace.globalStore ∧ trace.globalStore.elems = before.elems ∧
      trace.globalStore.datas = before.datas ∧ next.elems.val = [] ∧ next.datas.val = [] ∧
      next.globals.val.map (fun address => address.index.val) =
        trace.seed.globals.val.map (fun address => address.index.val) ++
          List.range' before.globals.length module.module.env.globals.val.length ∧
      ∃ produced, trace.globalStore.globals.val = before.globals.val ++ produced ∧
        GlobalSourceValues (decodeStore view code before) initialModule module.module.env.globals.val produced := by
  obtain ⟨preparedPrefix, preparedBound, preparedSource, preparedGlobals, preparedInstances,
    preparedElements, preparedData, preparedGlobalMap, preparedElementMap, preparedDataMap,
    preparedBindings, preparedImports, preparedSegments⟩ :=
    preparation_success memory allocator law view laws before trace.seed shape trace.maps
      (by simpa only [trace.source] using cache) before.instances.len
      trace.typed trace.functions trace.tabled trace.prepared trace.typeInst trace.funcInst trace.tableInst trace.inst
      trace.typeRun trace.functionRun trace.tableRun trace.memoryRun
  have room : trace.prepared.instances.length < Usize.max := by
    rw [preparedInstances]
    have instanceRoom := trace.instanceRoom
    scalar_tac
  have preparedAccounting : SegmentAccounting trace.prepared := by
    constructor
    · simpa only [preparedElements, preparedInstances] using accounted.elements
    · simpa only [preparedData, preparedInstances] using accounted.datas
  have emptyElements : trace.inst.elems.val = [] := by rw [preparedElementMap]; exact trace.maps.elements
  have emptyData : trace.inst.datas.val = [] := by rw [preparedDataMap]; exact trace.maps.data
  have publication := publish_prepared_instance trace.prepared trace.inst room
    preparedBindings preparedImports preparedSegments preparedAccounting emptyElements emptyData
  rw [trace.publicationRun] at publication
  simp only [WP.spec_ok] at publication
  obtain ⟨appended, publishedFound, publishedPrefix, publishedBindings, publishedImports, publishedSegments,
    publishedAccounting, publishedObjects⟩ := publication
  let published := {trace.prepared with instances := trace.publishedInstances}
  have found : published.instances.val[before.instances.len.val]? = some trace.inst := by
    simpa only [preparedInstances] using publishedFound
  have source : trace.inst.module = module := preparedSource.trans trace.source
  have globalCapacity : trace.inst.globals.length + trace.inst.module.module.env.globals.val.length ≤ Usize.max := by
    simpa only [preparedGlobalMap, preparedSource] using trace.maps.global_capacity
      (by simpa only [trace.source] using cache)
  have context : InitializerSourceContext (decodeStore view code before) initialModule published trace.inst := by
    apply InitializerSourceContext.of_maps view code before published trace.inst initialModule functionMap
    · simpa only [preparedGlobalMap] using globalMap
    · exact preparedGlobals
  have globalValid : ∀ global ∈ trace.inst.module.module.env.globals.val,
      Itasca.Module.Constants.Valid trace.inst.module.module.env global.init global.gtype.valtype := by
    rw [source]
    exact valid.globals
  have ordered := global_order_loop memory hooks floats allocator law before published platform
    before.instances.len 0#usize trace.inst (.Ok ()) (preparedPrefix.trans publishedPrefix) (by simp) found
    (by simpa only [source] using compiled) globalValid publishedBindings publishedImports publishedSegments
    (by change objectCount trace.prepared ≤ Usize.max; exact preparedBound) (by simp)
    (by simpa using globalCapacity) before.globals.length
    (trace.seed.globals.val.map (fun address => address.index.val))
    (by simpa only [published, preparedGlobals, preparedGlobalMap] using
      AddressOrder.refl before.globals.length (trace.seed.globals.val.map (fun address => address.index.val)))
  rw [trace.globalRun] at ordered
  simp only [WP.spec_ok] at ordered
  obtain ⟨orderedStore, orderedStatus, orderedEqual, _, _, _, _, orderedInst, orderedFound, _, addressOrder, _⟩ := ordered
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp orderedEqual
  have result := global_source_staging_loop memory hooks floats allocator law before published platform
    before.instances.len 0#usize trace.inst (.Ok ()) (preparedPrefix.trans publishedPrefix) (by simp) found
    (by simpa only [source] using compiled) globalValid publishedBindings publishedImports publishedSegments
    (by change objectCount trace.prepared ≤ Usize.max; exact preparedBound) (by simp)
    (by simpa using globalCapacity) (decodeStore view code before) initialModule storeWf frameWf context
    before.globals.val (by intro _; exact ⟨[], by simp [published, preparedGlobals], .nil⟩)
  change runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator
    {trace.prepared with instances := trace.publishedInstances} platform (.Ok ()) 0#usize before.instances.len
    ⦃ _ ⦄ at result
  rw [trace.globalRun] at result
  simp only [WP.spec_ok] at result
  obtain ⟨after, status, equal, staged, objectBound, accounting, metadata, next, nextFound, nextSource,
    bindings, imports, segments, elements, datas, elementMap, dataMap, sourceContext, values⟩ := result
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp equal
  have sameInstance : orderedInst = next := Option.some.inj (orderedFound.symm.trans nextFound)
  subst orderedInst
  obtain ⟨produced, stored, evaluated⟩ := values rfl
  refine ⟨next, nextFound, nextSource.trans source, metadata.resolve nextFound, bindings, imports, segments, sourceContext,
    staged, objectBound, accounting publishedAccounting, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact elements.trans preparedElements
  · exact datas.trans preparedData
  · rw [elementMap]; exact emptyElements
  · rw [dataMap]; exact emptyData
  · obtain ⟨count, total, mapped⟩ := addressOrder
    have outputLength := congrArg List.length stored
    have sourceLength := evaluated.length_eq
    have sameCount : count = module.module.env.globals.val.length := by
      simp only [List.length_append] at outputLength
      rw [source] at sourceLength
      change trace.globalStore.globals.val.length = before.globals.val.length + count at total
      omega
    simpa only [sameCount] using mapped
  · exact ⟨produced, stored, by simpa only [source] using evaluated⟩

end Itasca.Store

end

/-! ## Prepared Segment Source -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca.Module.Environment

private theorem address_order_total {start total count : Nat} {initial addresses : List Nat}
    (ordered : AddressOrder start initial total addresses) (totalEq : total = start + count) :
    addresses = initial ++ List.range' start count := by
  obtain ⟨actual, counted, mapped⟩ := ordered
  have same : actual = count := by omega
  simpa only [same] using mapped

/-- The actual committed preparation trace contains precisely the source
initializer values and data bytes, with segment addresses in source order. -/
theorem PreparedRun.segment_source_values {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (initialModule : moduleinst)
    (functionMap : initialModule.FUNCS = trace.inst.funcs.val.map (fun address => address.index.val))
    (globalMap : initialModule.GLOBALS = trace.seed.globals.val.map (fun address => address.index.val))
    (storeWf : wf_store (decodeStore view code before))
    (frameWf : wf_frame ⟨[], initialModule⟩) :
    ∃ globalInst next globals elements,
      trace.globalStore.instances.val[before.instances.len.val]? = some globalInst ∧
      ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      InitializerFunctionMetadata {trace.prepared with instances := trace.publishedInstances} trace.inst ready next ∧ next.globals = globalInst.globals ∧
      ready.globals.val = before.globals.val ++ globals ∧
      GlobalSourceValues (decodeStore view code before) initialModule module.module.env.globals.val globals ∧
      ready.elems.val = before.elems.val ++ elements ∧
      ElementSourceSegments (decodeStore view code before) initialModule module.module.env.elements.val elements ∧
      ready.datas.val.map decodeData = before.datas.val.map decodeData ++ module.module.tail.data.val.map sourceDataPayload ∧
      next.elems.val.map UScalar.val = List.range' before.elems.length module.module.env.elements.val.length ∧
      next.datas.val.map UScalar.val = List.range' before.datas.length module.module.tail.data.val.length ∧
      next.globals.val.map (fun address => address.index.val) = trace.seed.globals.val.map (fun address => address.index.val) ++
        List.range' before.globals.length module.module.env.globals.val.length := by
  obtain ⟨globalInst, globalFound, globalSource, globalMetadata, globalBindings, globalImports, globalSegments, globalContext,
    globalPrefix, globalBound, globalAccounting, globalElements, globalData, emptyElements, emptyData, globalAddresses,
    globals, globalsStored, globalValues⟩ := trace.global_source_context laws law shape accounted cache valid compiled
      code initialModule functionMap globalMap storeWf frameWf
  have elementCompiled : Compiler.InitializerMappings globalInst.module := by simpa only [globalSource] using compiled
  have elementValid : ∀ segment ∈ globalInst.module.module.env.elements.val,
      Itasca.Module.Segments.elementValid globalInst.module.module.env segment := by
    simpa only [globalSource] using valid.elements
  have elementCapacity : trace.globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
    simpa only [globalElements, globalSource, trace.source, Nat.sub_zero] using trace.elementCapacity
  have elementMapCapacity : globalInst.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
    have bound := globalInst.module.module.env.elements.property
    simpa [alloc.vec.Vec.length, emptyElements] using bound
  have elementsChecked := element_source_staging_loop memory hooks floats allocator law before trace.globalStore platform
    before.instances.len 0#usize globalInst (.Ok ()) globalPrefix (by simp) globalFound elementCompiled elementValid
    globalBindings globalImports globalSegments globalBound (by simp) elementCapacity elementMapCapacity
    (decodeStore view code before) initialModule storeWf frameWf globalContext before.elems.val
    (by intro _; exact ⟨[], by simp [globalElements], .nil⟩)
  rw [trace.elementRun] at elementsChecked
  simp only [WP.spec_ok] at elementsChecked
  obtain ⟨elementStore, elementStatus, parts, elementPrefix, elementBound, elementAccounting, elementMetadata,
    elementInst, elementFound, elementSource, elementBindings, elementImports, elementSegments,
    elementData, elementDataMap, elementGlobals, elementGlobalMap, elementContext, elementsPost⟩ := elementsChecked
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp parts
  obtain ⟨elements, elementsStored, elementValues⟩ := elementsPost rfl
  have elementOrder := element_order_loop memory hooks floats allocator law before trace.globalStore platform
    before.instances.len 0#usize globalInst (.Ok ()) globalPrefix (by simp) globalFound elementCompiled elementValid
    globalBindings globalImports globalSegments globalBound (by simp) elementCapacity elementMapCapacity
    before.elems.length [] (by simpa only [globalElements, emptyElements, List.map_nil] using AddressOrder.refl before.elems.length [])
  rw [trace.elementRun] at elementOrder
  simp only [WP.spec_ok] at elementOrder
  obtain ⟨elementStore, elementStatus, parts, _, _, _, _, actualInst, actualFound, _, ordered, _⟩ := elementOrder
  obtain ⟨rfl, _, rfl⟩ := (store_parts_inj _ _ _ _ _ _).mp parts
  have same : actualInst = elementInst := Option.some.inj (actualFound.symm.trans elementFound)
  subst actualInst
  have elementCount : trace.elementStore.elems.length = before.elems.length + globalInst.module.module.env.elements.val.length := by
    have count := elementValues.length_eq
    simp only [alloc.vec.Vec.length, elementsStored, List.length_append]
    exact congrArg (before.elems.val.length + ·) count.symm
  have elementAddresses := address_order_total ordered elementCount
  have dataSource : elementInst.module = module := elementSource.trans globalSource
  have dataCapacity : trace.elementStore.datas.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
    simpa only [elementData, globalData, dataSource, trace.source, Nat.sub_zero] using trace.dataCapacity
  have dataEmpty : elementInst.datas.val = [] := by rw [elementDataMap]; exact emptyData
  have dataMapCapacity : elementInst.datas.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
    have bound := elementInst.module.module.tail.data.property
    simpa [alloc.vec.Vec.length, dataEmpty] using bound
  have dataChecked := data_payload_loop memory allocator law before trace.elementStore before.instances.len 0#usize elementInst (.Ok ())
    elementPrefix (by simp) elementFound elementBindings elementImports elementSegments elementBound (by simp)
    dataCapacity dataMapCapacity (before.datas.val.map decodeData)
    (by intro _; simp [elementData, globalData])
  rw [trace.dataRun] at dataChecked
  simp only [WP.spec_ok] at dataChecked
  obtain ⟨dataStore, dataStatus, parts, _, _, _, dataMetadata, ⟨next, nextFound, nextSource, _, _, _,
    dataElements, dataElementMap, dataGlobals, dataGlobalMap⟩, dataValues⟩ := dataChecked
  obtain ⟨rfl, rfl⟩ := (store_state_parts_inj _ _ _ _).mp parts
  have dataOrder := data_order_loop memory allocator law before trace.elementStore before.instances.len 0#usize elementInst (.Ok ())
    elementPrefix (by simp) elementFound elementBindings elementImports elementSegments elementBound (by simp)
    dataCapacity dataMapCapacity before.datas.length []
    (by simpa only [elementData, globalData, dataEmpty, List.map_nil] using AddressOrder.refl before.datas.length [])
  rw [trace.dataRun] at dataOrder
  simp only [WP.spec_ok] at dataOrder
  obtain ⟨dataStore, dataStatus, parts, _, _, _, _, actualInst, actualFound, _, dataOrdered, _⟩ := dataOrder
  obtain ⟨rfl, rfl⟩ := (store_state_parts_inj _ _ _ _).mp parts
  have same : actualInst = next := Option.some.inj (actualFound.symm.trans nextFound)
  subst actualInst
  have dataCount : trace.dataStore.datas.length = before.datas.length + elementInst.module.module.tail.data.val.length := by
    have count := congrArg List.length (dataValues rfl)
    simpa only [List.length_map, List.length_append] using count
  have dataAddresses := address_order_total dataOrdered dataCount
  refine ⟨globalInst, next, globals, elements, globalFound, ?_, nextSource.trans dataSource, ?_,
    dataGlobalMap.trans elementGlobalMap, ?_, globalValues, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [trace.committed] using nextFound
  · have metadata := globalMetadata.trans ((elementMetadata.resolve elementFound).trans (dataMetadata.resolve nextFound))
    simp only [trace.committed]
    exact ⟨metadata.identity, metadata.functions, metadata.signatures, metadata.source, metadata.typeMap,
      metadata.functionMap, metadata.tables, metadata.tableMap, metadata.memories, metadata.memoryMap, metadata.instanceCount⟩
  · simpa only [trace.committed, dataGlobals, elementGlobals] using globalsStored
  · simpa only [trace.committed, dataElements] using elementsStored
  · simpa only [globalSource] using elementValues
  · simpa only [trace.committed, dataSource] using dataValues rfl
  · simpa only [dataElementMap, globalSource, List.nil_append] using elementAddresses
  · simpa only [dataSource, List.nil_append] using dataAddresses
  · simpa only [dataGlobalMap, elementGlobalMap] using globalAddresses
end Itasca.Store

end

/-! ## Prepared Allocation Content -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

/-- Exact six-space source allocation content, obtained from the actual retained
preparation calls. Function decoding includes the fresh source interpretation
and proves that all pre-existing function instances keep their old decoding. -/
theorem PreparedRun.allocation_content {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (raw : Binary.Module)
    (cache : Module.Environment.Cache module.module.env raw.tables raw.memories)
    (matched : Module.Elaboration.Matches module.module.env module.module.tail raw)
    (lengths : raw.functions.length = raw.codes.length)
    (valid : Module.Environment.Valid module.module.env) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (initialModule : moduleinst)
    (functionMap : initialModule.FUNCS = trace.inst.funcs.val.map (fun address => address.index.val))
    (globalMap : initialModule.GLOBALS = trace.seed.globals.val.map (fun address => address.index.val))
    (storeWf : wf_store (decodeStore view code before)) (frameWf : wf_frame ⟨[], initialModule⟩) :
    ∃ next globals elements,
      ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      GlobalSourceValues (decodeStore view code before) initialModule module.module.env.globals.val globals ∧
      ElementSourceSegments (decodeStore view code before) initialModule module.module.env.elements.val elements ∧
      decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready =
        Spec.allocationStore (decodeStore view code before) (decodeInstance ready next)
          (List.zipWith CodeEntry.function raw.functions raw.codes) (globals.map decodeGlobal)
          (raw.tables.map Translation.Environment.tableType) (raw.memories.map Translation.Environment.memType)
          (elements.map decodeElement) (module.module.tail.data.val.map sourceDataPayload) ∧
      (decodeInstance ready next).TYPES = raw.types.map Translation.Environment.funcType ∧
      next.funcs.val.map (fun a => a.index.val) = trace.seed.funcs.val.map (fun a => a.index.val) ++
        List.range' before.funcs.length raw.functions.length ∧
      next.globals.val.map (fun a => a.index.val) = trace.seed.globals.val.map (fun a => a.index.val) ++
        List.range' before.globals.length globals.length ∧
      next.tables.val.map (fun a => a.index.val) = trace.seed.tables.val.map (fun a => a.index.val) ++
        List.range' before.tables.length raw.tables.length ∧
      next.memories.val.map (fun a => a.index.val) = trace.seed.memories.val.map (fun a => a.index.val) ++
        List.range' before.memories.length raw.memories.length ∧
      next.elems.val.map UScalar.val = List.range' before.elems.length elements.length ∧
      next.datas.val.map UScalar.val = List.range' before.datas.length module.module.tail.data.val.length := by
  obtain ⟨globalInst, next, globals, elements, globalFound, found, source, metadata, globalMapEq,
    globalsStored, globalValues, elementsStored, elementValues, datasStored, elementAddresses,
    dataAddresses, globalAddresses⟩ := trace.segment_source_values laws law shape accounted cache valid compiled
      code initialModule functionMap globalMap storeWf frameWf
  obtain ⟨typedFunctions, typeSource, _, _, payload, _, functionAddresses⟩ := trace.function_payload law shape cache
  obtain ⟨preparedFunctions, preparedTypes, preparedFunctionMap, preparedTypeMap, preparedSource⟩ :=
    trace.preparation_metadata laws law shape cache
  obtain ⟨tablesStored, memoriesStored, tableAddresses, memoryAddresses, _, _⟩ :=
    trace.table_memory_allocations laws law shape cache
  obtain ⟨actual, actualFound, _, readyShape, _, retained, _, codeMetadata⟩ :=
    trace.shape_data laws law shape accounted cache valid compiled
  have actualFound' : ready.instances.val[before.instances.len.val]? = some actual := by
    simpa only [trace.committed] using actualFound
  have same : actual = next := Option.some.inj (actualFound'.symm.trans found)
  subst actual
  have indices : module.module.env.func_type_indices.val = raw.functions := by
    exact (congrArg Binary.Module.functions matched.1).symm
  have sourceTypes : module.module.env.types.val = raw.types := by
    exact (congrArg Binary.Module.types matched.1).symm
  have rawPayload : FunctionPayload trace.typed trace.functions trace.typeInst before.instances.len raw.functions.length := by
    simpa only [indices] using payload
  have allocatedFunctions := canonical_function_payload_decode raw lengths
    (by simpa only [typeSource] using indices) rawPayload code ready next found
    (metadata.typeMap.trans preparedTypeMap)
  have oldFunctions : before.funcs.val.map
      (decodeFunction (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready) =
      before.funcs.val.map (decodeFunction code before) := by
    apply List.map_congr_left
    intro function present
    have retainedFunction := decode_function_prefix
      (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) before trace.dataStore retained view shape function present
    have agrees := decode_function_code_agrees (install_code_agrees before code (Compiler.sourceFunctions raw)) function
    have charge : decodeFunction (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready function =
        decodeFunction (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) trace.dataStore function := by
      simp only [trace.committed, decodeFunction, decodeInstance]
    exact charge.trans (retainedFunction.trans agrees)
  have functionsStored : ready.funcs.val.map
      (decodeFunction (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready) =
      before.funcs.val.map (decodeFunction code before) ++
      (List.zipWith CodeEntry.function raw.functions raw.codes).map (Spec.allocationFunction (decodeInstance ready next)) := by
    simpa only [metadata.functions, preparedFunctions, typedFunctions, oldFunctions] using allocatedFunctions
  have types := type_entries_decoded codeMetadata.type_entries
  refine ⟨next, globals, elements, found, source, globalValues, elementValues, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dataAddresses⟩
  · unfold decodeStore Spec.allocationStore
    simp only [functionsStored, globalsStored, elementsStored, List.map_append,
      metadata.tables, metadata.memories, tablesStored, memoriesStored, List.map_map, Function.comp_def, datasStored]
  · simpa only [decodeInstance, source, sourceTypes, funext decode_func_type_source] using types
  · simpa only [metadata.functionMap, preparedFunctionMap, indices] using functionAddresses
  · simpa only [globalValues.length_eq] using globalAddresses
  · simpa only [metadata.tableMap] using tableAddresses
  · simpa only [metadata.memoryMap] using memoryAddresses
  · simpa only [elementValues.length_eq] using elementAddresses
end Itasca.Store

end

/-! ## Prepared Allocation -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

/-- The source initializer frame contains imported globals and the complete
function address map, before any defined global or segment is allocated. -/
def allocationInitial {M : Type} (raw : Binary.Module) (before : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) : moduleinst :=
  ⟨raw.types.map Translation.Environment.funcType,
    seed.funcs.val.map (fun address => address.index.val) ++ List.range' before.funcs.length raw.functions.length,
    seed.globals.val.map (fun address => address.index.val), [], [], [], [], []⟩

theorem allocation_initial_wf {M : Type} (raw : Binary.Module) (before : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) : wf_moduleinst (allocationInitial raw before seed) := by
  constructor
  simp [Forall]

private theorem function_bounds (indices : List U32) (entries : List Binary.Code) (bound : Nat)
    (valid : ∀ index ∈ indices, index.val < bound) :
    ∀ function ∈ List.zipWith CodeEntry.function indices entries, Spec.allocationFunctionIndex function < bound := by
  induction indices generalizing entries with
  | nil => simp
  | cons index indices ih =>
    cases entries with
    | nil => simp
    | cons entry entries =>
      intro function member
      simp only [List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact valid index (by simp)
      · exact ih entries (fun index present => valid index (by simp [present])) function member

/-- Actual linking and preparation derive the generated allocator judgment.
All source code, initializer values, imported addresses, exports, and allocation
orders are recovered from checked static metadata and actual call equalities. -/
theorem LinkedPreparedRun.source_allocation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {imports : Slice runtime.Extern}
    {platform : P} {ready : runtime.store.Store M}
    (trace : LinkedPreparedRun memory hooks floats allocator view before module imports platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (raw : Binary.Module)
    (cache : Module.Environment.Cache module.module.env raw.tables raw.memories)
    (matched : Module.Elaboration.Matches module.module.env module.module.tail raw)
    (elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (valid : Module.Environment.Valid module.module.env) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (oldSyntax : StoreSyntax code before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ∃ next globals elements,
      ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      GlobalSourceValues (decodeStore view code before) (allocationInitial raw before trace.seed)
        module.module.env.globals.val globals ∧
      ElementSourceSegments (decodeStore view code before) (allocationInitial raw before trace.seed)
        module.module.env.elements.val elements ∧
      fun_allocmodule (decodeStore view code before) (Module.Elaboration.moduleOf raw)
        (imports.val.map decodeExternal) ((globals.map decodeGlobal).map globalinst.VALUE)
        ((elements.map decodeElement).map eleminst.REFS)
        (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready,
          decodeInstance ready next) := by
  have storeWf := decode_store_wf view code before shape oldSyntax
  have frameWf : wf_frame ⟨[], allocationInitial raw before trace.seed⟩ := by
    constructor
    · simp [Forall]
    · exact allocation_initial_wf raw before trace.seed
  obtain ⟨_, _, _, _, _, _, functionAddresses⟩ := trace.toPreparedRun.function_payload law shape cache
  obtain ⟨_, _, functionMap, _, _⟩ := trace.toPreparedRun.preparation_metadata laws law shape cache
  have indices : module.module.env.func_type_indices.val = raw.functions :=
    (congrArg Binary.Module.functions matched.1).symm
  have initialFunctions : (allocationInitial raw before trace.seed).FUNCS = trace.inst.funcs.val.map (fun a => a.index.val) := by
    simpa only [allocationInitial, functionMap, indices] using functionAddresses.symm
  obtain ⟨next, globals, elements, found, source, globalValues, elementValues, content, typeMap,
    functionMap, globalMap, tableMap, memoryMap, elementMap, dataMap⟩ :=
    trace.toPreparedRun.allocation_content laws law shape accounted raw cache matched elaborated.code_count valid compiled
      code (allocationInitial raw before trace.seed) initialFunctions rfl storeWf frameWf
  obtain ⟨actual, actualFound, _, readyShape, _, _, _, _⟩ := trace.toPreparedRun.shape_data laws law shape accounted cache valid compiled
  have sourceSyntax := instance_syntax_source code before.instances.len.val next raw elaborated typed
    (by simpa only [source] using matched)
  have instWf := decode_instance_wf _ _ ready next sourceSyntax
  have importsMapped := trace.external_maps laws shape cache handles
  obtain ⟨importFunctions, importGlobals, importTables, importMemories⟩ := importsMapped.source imports.val trace.seed
  have exports := exports_source_raw ready next (readyShape.instances next (List.mem_of_getElem? found))
    (by simpa only [source] using valid) _ _ sourceSyntax raw (by simpa only [source] using matched)
  have sourceWf : wf_module (Module.Elaboration.moduleOf raw) := by cases typed; assumption
  have functionsWf : Forall wf_func (List.zipWith CodeEntry.function raw.functions raw.codes) := by
    cases sourceWf; assumption
  have tablesWf : Forall wf_tabletype (raw.tables.map Translation.Environment.tableType) := by
    have all : Forall wf_table (raw.tables.map Module.Elaboration.table) := by cases sourceWf; assumption
    intro value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have current := all _ (List.mem_map.mpr ⟨original, present, rfl⟩)
    cases current; assumption
  have memoriesWf : Forall wf_memtype (raw.memories.map Translation.Environment.memType) := by
    have all : Forall wf_mem (raw.memories.map Module.Elaboration.memory) := by cases sourceWf; assumption
    intro value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have current := all _ (List.mem_map.mpr ⟨original, present, rfl⟩)
    cases current; assumption
  have globalsWf : Forall wf_globalinst (globals.map decodeGlobal) := by
    intro value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact .globalinst_case_ _ _ (decode_words_wf _ _ _)
  have datasWf : Forall wf_datainst (module.module.tail.data.val.map sourceDataPayload) := by
    intro value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact .datainst_case_ _ (decode_bytes_wf original.init.val)
  have rawGlobals : raw.globals = module.module.env.globals.val := congrArg Binary.Module.globals matched.1
  have rawElements : raw.elements = module.module.env.elements.val.map Module.Environment.rawElement := congrArg Binary.Module.elements matched.1
  have rawDatas : raw.data = module.module.tail.data.val.map Module.Data.raw := congrArg Binary.Module.data matched.1
  have allocated := Spec.allocate_module (decodeStore view code before) (Module.Elaboration.moduleOf raw)
    (imports.val.map decodeExternal) (decodeInstance ready next)
    (raw.types.map Translation.Environment.funcType) (raw.imports.map (Module.Elaboration.importDecl raw.types))
    (List.zipWith CodeEntry.function raw.functions raw.codes) (globals.map decodeGlobal)
    (raw.tables.map Translation.Environment.tableType) (raw.memories.map Translation.Environment.memType)
    (elements.map decodeElement) (module.module.tail.data.val.map sourceDataPayload)
    (module.module.env.globals.val.map fun original => Module.Constants.expression original.init)
    (module.module.env.elements.val.map fun original => original.init.val.map Module.Constants.expression)
    (module.module.env.elements.val.map fun original => Module.Segments.elementMode original.mode)
    (module.module.tail.data.val.map fun original => Module.Segments.dataMode original.mode)
    (raw.start.map Module.Elaboration.start) (raw.exports.map Module.Elaboration.exportDecl) (decodeInstance ready next).EXPORTS
    (trace.seed.funcs.val.map fun a => a.index.val) (trace.seed.globals.val.map fun a => a.index.val)
    (trace.seed.tables.val.map fun a => a.index.val) (trace.seed.memories.val.map fun a => a.index.val)
    ?sourceEq ?layout importFunctions importGlobals importTables importMemories exports
    storeWf sourceWf instWf functionsWf ?functionBounds globalsWf tablesWf memoriesWf datasWf
  · refine ⟨next, globals, elements, found, source, globalValues, elementValues, ?_⟩
    simpa only [← content] using allocated
  case sourceEq =>
    unfold Module.Elaboration.moduleOf
    rw [rawGlobals, globalValues.syntax, rawElements, elementValues.syntax, rawDatas, source_data_payload_syntax]
    simp only [List.map_map, Function.comp_def]
    rfl
  case layout =>
    have sameTypes : (decodeInstance ready next).TYPES = raw.types.map Translation.Environment.funcType := typeMap
    have sourceCount : (List.zipWith CodeEntry.function raw.functions raw.codes).length = raw.functions.length := by
      simp only [List.length_zipWith, elaborated.code_count, Nat.min_self]
    simp only [decodeInstance, decodeStore, List.length_map, sourceCount,
      functionMap, globalMap, tableMap, memoryMap, elementMap, dataMap]
    congr 1
  case functionBounds =>
    rw [typeMap]
    simpa only [List.length_map] using function_bounds raw.functions raw.codes raw.types.length elaborated.functions
end Itasca.Store

end

/-! ## Prepared Source Instantiation -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std Itasca

/-- The actual preparation cutpoint is the generated source instantiation
configuration. Its constants, exports, fresh addresses and all six allocation
spaces are derived from actual calls; the remaining source program is exactly
segment initialization followed by the optional start call. -/
theorem LinkedPreparedRun.source_instantiation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {imports : Slice runtime.Extern}
    {platform : P} {ready : runtime.store.Store M}
    (trace : LinkedPreparedRun memory hooks floats allocator view before module imports platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (raw : Binary.Module)
    (cache : Module.Environment.Cache module.module.env raw.tables raw.memories)
    (matched : Module.Elaboration.Matches module.module.env module.module.tail raw)
    (elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    {R bytes} (encoded : Binary.ModuleEncodingWith R raw bytes)
    (valid : Module.Environment.Valid module.module.env) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (oldSyntax : StoreSyntax code before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ∃ next, ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      fun_instantiate (decodeStore view code before) (Module.Elaboration.moduleOf raw) (imports.val.map decodeExternal)
        ⟨⟨decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready,
          ⟨[], decodeInstance ready next⟩⟩,
          (Spec.Segment.elementPrograms (raw.elements.map Module.Elaboration.element)).flatten.map admininstr_instr ++
          ((Spec.Segment.dataPrograms (raw.data.map Module.Data.translate)).flatten.map admininstr_instr ++
            (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩ := by
  obtain ⟨next, globals, elements, found, source, globalValues, elementValues, allocated⟩ :=
    trace.source_allocation laws law shape accounted raw cache matched elaborated typed valid compiled code oldSyntax handles
  obtain ⟨importFunctions, importGlobals, _, _⟩ := (trace.external_maps laws shape cache handles).source imports.val trace.seed
  have rawGlobals : raw.globals = module.module.env.globals.val := congrArg Binary.Module.globals matched.1
  have rawElements : raw.elements = module.module.env.elements.val.map Module.Environment.rawElement := congrArg Binary.Module.elements matched.1
  refine ⟨next, found, source, ?_⟩
  apply Compiler.source_instantiate encoded elaborated typed (decodeStore view code before)
    (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready)
    (imports.val.map decodeExternal) (decodeInstance ready next) (allocationInitial raw before trace.seed)
    (trace.seed.funcs.val.map fun address => address.index.val) (trace.seed.globals.val.map fun address => address.index.val)
    ((globals.map decodeGlobal).map globalinst.VALUE) ((elements.map decodeElement).map eleminst.REFS)
    importFunctions importGlobals ?_ ?_ ?_ allocated (decode_store_wf view code before shape oldSyntax)
  · simp only [allocationInitial, decodeStore, List.length_map, List.length_zipWith, elaborated.code_count,
      Nat.min_self, List.range'_eq_map_range]
  · simpa only [rawGlobals] using globalValues.raw_evaluations
  · simpa only [rawElements] using elementValues.raw_evaluations
end Itasca.Store

end

end

/-! ## PreparedExportBounds -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The actual publication and initializer staging calls preserve old export
bounds and install the fresh bounds established by module validation. -/
theorem PreparedRun.export_bounds {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Itasca.Module.Environment.Cache module.module.env tables memories)
    (valid : Itasca.Module.Environment.Valid module.module.env)
    (compiled : Compiler.InitializerMappings module) (old : ExportBounds before) : ExportBounds ready := by
  obtain ⟨inst,found,source,_,_,retained,_,_⟩ := trace.shape_data laws law shape accounted cache valid compiled
  obtain ⟨actual,actualFound,_,count,_,_⟩ := trace.global_types laws law shape accounted cache valid compiled
  have bounded : ExportBounds trace.dataStore := by
    apply old.staged retained
    · simpa only [trace.committed] using Nat.le_of_eq count
    · intro selected selectedFound
      have same : selected = inst := Option.some.inj (selectedFound.symm.trans found)
      subst selected
      rw [source]
      exact module_export_bounds valid
  exact bounded.instances_eq (by simp only [trace.committed])
end Itasca.Store

end

/-! ## NoStart -/

section

/-!
Structural store validity provides the finite constant-read bindings needed by the compiler's synthetic initialization code.

Main declarations: `Shape.initializer_bindings`.
-/

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Structural store validity provides the finite constant-read bindings needed
by the compiler's synthetic initialization code. -/
theorem _root_.Itasca.Representation.Shape.initializer_bindings {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (shape : Shape view store) (found : inst ∈ store.instances.val) :
    InitializerBindings store inst := by
  have instanceShape := shape.instances inst found
  refine ⟨?_, shape.globals⟩
  intro address member
  exact (instanceShape.2.2.2.2.2.2.2.2.1 address member).2

end Itasca.Store

end

end

end
