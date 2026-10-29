import Itasca.Runtime.Store.Instantiation.LinkedPreparedRun
import Itasca.Runtime.Store.Linking.LinkLoop
import Itasca.Runtime.Store.Instantiation.PreparedRun
import Itasca.Runtime.Store.Preparation.PreparationFunctionPayload
import Itasca.Runtime.Store.Preparation.PreparationSuccess
import Itasca.Runtime.Store.Instantiation.PublishInstance
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Store.Api.GlobalLoopCertificates
import Itasca.Runtime.Store.Initialization.ElementSourceStaging
import Itasca.Runtime.Store.Initialization.ElementOrderLoop
import Itasca.Runtime.Store.Initialization.DataLoopCertificates
import Itasca.Runtime.Store.Preparation.StagingTypeCertificates
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Instantiation.PreparedRunCertificates
import Itasca.Runtime.Store.Invariant.SourceFunctionAllocation
import Itasca.Runtime.Store.Invariant.SourceBindings
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.SourceAllocationLists
import Itasca.Runtime.Spec.AllocationModule
import Itasca.Runtime.Store.Invariant.SourceExports
import Itasca.Runtime.Compiler.Module.SourceInstantiation

/-!
Source instantiation from the prepared concrete allocation. Function/global/segment payloads and external maps establish the source allocation step, then the prepared initialization composes it into source instantiation without executing start code.
-/

/-! ## Prepared External Maps -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

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
end Itasca.Runtime.Store

end

/-! ## Prepared Function Payload -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

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
end Itasca.Runtime.Store

end

/-! ## Prepared Global Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

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
    (valid : Valid module.module.env module.profile) (compiled : Compiler.InitializerMappings module)
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
      Itasca.ModuleConstants.Valid trace.inst.module.module.env global.init global.gtype.valtype := by
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

end Itasca.Runtime.Store

end

/-! ## Prepared Segment Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

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
    (valid : Valid module.module.env module.profile) (compiled : Compiler.InitializerMappings module)
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
      Itasca.ModuleSegments.elementValid globalInst.module.module.env segment := by
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
end Itasca.Runtime.Store

end

/-! ## Prepared Allocation Content -/

section

namespace Itasca.Runtime.Store
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
    (raw : ModuleBinary.Module)
    (cache : ModuleEnv.Cache module.module.env raw.tables raw.memories)
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (lengths : raw.functions.length = raw.codes.length)
    (valid : ModuleEnv.Valid module.module.env module.profile) (compiled : Compiler.InitializerMappings module)
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
          (raw.tables.map EnvTranslation.tableType) (raw.memories.map EnvTranslation.memType)
          (elements.map decodeElement) (module.module.tail.data.val.map sourceDataPayload) ∧
      (decodeInstance ready next).TYPES = raw.types.map EnvTranslation.funcType ∧
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
    exact (congrArg ModuleBinary.Module.functions matched.1).symm
  have sourceTypes : module.module.env.types.val = raw.types := by
    exact (congrArg ModuleBinary.Module.types matched.1).symm
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
end Itasca.Runtime.Store

end

/-! ## Prepared Allocation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- The source initializer frame contains imported globals and the complete
function address map, before any defined global or segment is allocated. -/
def allocationInitial {M : Type} (raw : ModuleBinary.Module) (before : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) : moduleinst :=
  ⟨raw.types.map EnvTranslation.funcType,
    seed.funcs.val.map (fun address => address.index.val) ++ List.range' before.funcs.length raw.functions.length,
    seed.globals.val.map (fun address => address.index.val), [], [], [], [], []⟩

theorem allocation_initial_wf {M : Type} (raw : ModuleBinary.Module) (before : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) : wf_moduleinst (allocationInitial raw before seed) := by
  constructor
  simp [Forall]

private theorem function_bounds (indices : List U32) (entries : List ModuleBinary.Code) (bound : Nat)
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
    (raw : ModuleBinary.Module)
    (cache : ModuleEnv.Cache module.module.env raw.tables raw.memories)
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (valid : ModuleEnv.Valid module.module.env module.profile) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (oldSyntax : StoreSyntax code before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ∃ next globals elements,
      ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      GlobalSourceValues (decodeStore view code before) (allocationInitial raw before trace.seed)
        module.module.env.globals.val globals ∧
      ElementSourceSegments (decodeStore view code before) (allocationInitial raw before trace.seed)
        module.module.env.elements.val elements ∧
      fun_allocmodule (decodeStore view code before) (ModuleElaboration.moduleOf raw)
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
    (congrArg ModuleBinary.Module.functions matched.1).symm
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
  have sourceWf : wf_module (ModuleElaboration.moduleOf raw) := by cases typed; assumption
  have functionsWf : Forall wf_func (List.zipWith CodeEntry.function raw.functions raw.codes) := by
    cases sourceWf; assumption
  have tablesWf : Forall wf_tabletype (raw.tables.map EnvTranslation.tableType) := by
    have all : Forall wf_table (raw.tables.map ModuleElaboration.table) := by cases sourceWf; assumption
    intro value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have current := all _ (List.mem_map.mpr ⟨original, present, rfl⟩)
    cases current; assumption
  have memoriesWf : Forall wf_memtype (raw.memories.map EnvTranslation.memType) := by
    have all : Forall wf_mem (raw.memories.map ModuleElaboration.memory) := by cases sourceWf; assumption
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
  have rawGlobals : raw.globals = module.module.env.globals.val := congrArg ModuleBinary.Module.globals matched.1
  have rawElements : raw.elements = module.module.env.elements.val.map ModuleEnv.rawElement := congrArg ModuleBinary.Module.elements matched.1
  have rawDatas : raw.data = module.module.tail.data.val.map ModuleData.raw := congrArg ModuleBinary.Module.data matched.1
  have allocated := Spec.allocate_module (decodeStore view code before) (ModuleElaboration.moduleOf raw)
    (imports.val.map decodeExternal) (decodeInstance ready next)
    (raw.types.map EnvTranslation.funcType) (raw.imports.map (ModuleElaboration.importDecl raw.types))
    (List.zipWith CodeEntry.function raw.functions raw.codes) (globals.map decodeGlobal)
    (raw.tables.map EnvTranslation.tableType) (raw.memories.map EnvTranslation.memType)
    (elements.map decodeElement) (module.module.tail.data.val.map sourceDataPayload)
    (module.module.env.globals.val.map fun original => ModuleConstants.expression original.init)
    (module.module.env.elements.val.map fun original => original.init.val.map ModuleConstants.expression)
    (module.module.env.elements.val.map fun original => ModuleSegments.elementMode original.mode)
    (module.module.tail.data.val.map fun original => ModuleSegments.dataMode original.mode)
    (raw.start.map ModuleElaboration.start) (raw.exports.map ModuleElaboration.exportDecl) (decodeInstance ready next).EXPORTS
    (trace.seed.funcs.val.map fun a => a.index.val) (trace.seed.globals.val.map fun a => a.index.val)
    (trace.seed.tables.val.map fun a => a.index.val) (trace.seed.memories.val.map fun a => a.index.val)
    ?sourceEq ?layout importFunctions importGlobals importTables importMemories exports
    storeWf sourceWf instWf functionsWf ?functionBounds globalsWf tablesWf memoriesWf datasWf
  · refine ⟨next, globals, elements, found, source, globalValues, elementValues, ?_⟩
    simpa only [← content] using allocated
  case sourceEq =>
    unfold ModuleElaboration.moduleOf
    rw [rawGlobals, globalValues.syntax, rawElements, elementValues.syntax, rawDatas, source_data_payload_syntax]
    simp only [List.map_map, Function.comp_def]
    rfl
  case layout =>
    have sameTypes : (decodeInstance ready next).TYPES = raw.types.map EnvTranslation.funcType := typeMap
    have sourceCount : (List.zipWith CodeEntry.function raw.functions raw.codes).length = raw.functions.length := by
      simp only [List.length_zipWith, elaborated.code_count, Nat.min_self]
    simp only [decodeInstance, decodeStore, List.length_map, sourceCount,
      functionMap, globalMap, tableMap, memoryMap, elementMap, dataMap]
    congr 1
  case functionBounds =>
    rw [typeMap]
    simpa only [List.length_map] using function_bounds raw.functions raw.codes raw.types.length elaborated.functions
end Itasca.Runtime.Store

end

/-! ## Prepared Source Instantiation -/

section

namespace Itasca.Runtime.Store
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
    (raw : ModuleBinary.Module)
    (cache : ModuleEnv.Cache module.module.env raw.tables raw.memories)
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    {R bytes profile} (encoded : ModuleBinary.ModuleEncodingWith R raw bytes profile)
    (valid : ModuleEnv.Valid module.module.env module.profile) (compiled : Compiler.InitializerMappings module)
    (code : CodeInterpretation) (oldSyntax : StoreSyntax code before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ∃ next, ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      fun_instantiate (decodeStore view code before) (ModuleElaboration.moduleOf raw) (imports.val.map decodeExternal)
        ⟨⟨decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready,
          ⟨[], decodeInstance ready next⟩⟩,
          (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
          ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
            (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩ := by
  obtain ⟨next, globals, elements, found, source, globalValues, elementValues, allocated⟩ :=
    trace.source_allocation laws law shape accounted raw cache matched elaborated typed valid compiled code oldSyntax handles
  obtain ⟨importFunctions, importGlobals, _, _⟩ := (trace.external_maps laws shape cache handles).source imports.val trace.seed
  have rawGlobals : raw.globals = module.module.env.globals.val := congrArg ModuleBinary.Module.globals matched.1
  have rawElements : raw.elements = module.module.env.elements.val.map ModuleEnv.rawElement := congrArg ModuleBinary.Module.elements matched.1
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
end Itasca.Runtime.Store

end
