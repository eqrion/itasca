import Exec.Store.Instantiation.PreparedGlobalSource
import Exec.Store.Initialization.ElementSourceStaging
import Exec.Store.Initialization.ElementOrderLoop
import Exec.Store.Initialization.DataPayloadLoop
import Exec.Store.Initialization.DataOrderLoop
import Exec.Store.Preparation.StagingTypeCertificates
namespace Exec.Store
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
    (valid : Valid module.module.env module.profile) (compiled : Code.InitializerMappings module)
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
      next.elements.val.map UScalar.val = List.range' before.elems.length module.module.env.elements.val.length ∧
      next.data.val.map UScalar.val = List.range' before.datas.length module.module.tail.data.val.length ∧
      next.globals.val.map (fun address => address.index.val) = trace.seed.globals.val.map (fun address => address.index.val) ++
        List.range' before.globals.length module.module.env.globals.val.length := by
  obtain ⟨globalInst, globalFound, globalSource, globalMetadata, globalBindings, globalImports, globalSegments, globalContext,
    globalPrefix, globalBound, globalAccounting, globalElements, globalData, emptyElements, emptyData, globalAddresses,
    globals, globalsStored, globalValues⟩ := trace.global_source_context laws law shape accounted cache valid compiled
      code initialModule functionMap globalMap storeWf frameWf
  have elementCompiled : Code.InitializerMappings globalInst.module := by simpa only [globalSource] using compiled
  have elementValid : ∀ segment ∈ globalInst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid globalInst.module.module.env segment := by
    simpa only [globalSource] using valid.elements
  have elementCapacity : trace.globalStore.elems.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
    simpa only [globalElements, globalSource, trace.source, Nat.sub_zero] using trace.elementCapacity
  have elementMapCapacity : globalInst.elements.length + (globalInst.module.module.env.elements.val.length - 0) ≤ Usize.max := by
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
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp parts
  obtain ⟨elements, elementsStored, elementValues⟩ := elementsPost rfl
  have elementOrder := element_order_loop memory hooks floats allocator law before trace.globalStore platform
    before.instances.len 0#usize globalInst (.Ok ()) globalPrefix (by simp) globalFound elementCompiled elementValid
    globalBindings globalImports globalSegments globalBound (by simp) elementCapacity elementMapCapacity
    before.elems.length [] (by simpa only [globalElements, emptyElements, List.map_nil] using AddressOrder.refl before.elems.length [])
  rw [trace.elementRun] at elementOrder
  simp only [WP.spec_ok] at elementOrder
  obtain ⟨elementStore, elementStatus, parts, _, _, _, _, actualInst, actualFound, _, ordered, _⟩ := elementOrder
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp parts
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
  have dataEmpty : elementInst.data.val = [] := by rw [elementDataMap]; exact emptyData
  have dataMapCapacity : elementInst.data.length + (elementInst.module.module.tail.data.val.length - 0) ≤ Usize.max := by
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
  obtain ⟨rfl, rfl⟩ := (storeStateParts_inj _ _ _ _).mp parts
  have dataOrder := data_order_loop memory allocator law before trace.elementStore before.instances.len 0#usize elementInst (.Ok ())
    elementPrefix (by simp) elementFound elementBindings elementImports elementSegments elementBound (by simp)
    dataCapacity dataMapCapacity before.datas.length []
    (by simpa only [elementData, globalData, dataEmpty, List.map_nil] using AddressOrder.refl before.datas.length [])
  rw [trace.dataRun] at dataOrder
  simp only [WP.spec_ok] at dataOrder
  obtain ⟨dataStore, dataStatus, parts, _, _, _, _, actualInst, actualFound, _, dataOrdered, _⟩ := dataOrder
  obtain ⟨rfl, rfl⟩ := (storeStateParts_inj _ _ _ _).mp parts
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
end Exec.Store
