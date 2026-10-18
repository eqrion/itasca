import Exec.Store.Instantiation.PreparedRun
import Exec.Store.Preparation.PreparationSuccess
import Exec.Store.Instantiation.PublishInstance
import Exec.Store.Linking.LinkedOwners
import Exec.Store.Api.GlobalSourceLoop
import Exec.Store.Api.GlobalOrderLoop
namespace Exec.Store
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
    (valid : Valid module.module.env module.profile) (compiled : Code.InitializerMappings module)
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
      trace.globalStore.datas = before.datas ∧ next.elements.val = [] ∧ next.data.val = [] ∧
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
  have emptyElements : trace.inst.elements.val = [] := by rw [preparedElementMap]; exact trace.maps.elements
  have emptyData : trace.inst.data.val = [] := by rw [preparedDataMap]; exact trace.maps.data
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
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp orderedEqual
  have result := global_source_staging_loop memory hooks floats allocator law before published platform
    before.instances.len 0#usize trace.inst (.Ok ()) (preparedPrefix.trans publishedPrefix) (by simp) found
    (by simpa only [source] using compiled) globalValid publishedBindings publishedImports publishedSegments
    (by change objectCount trace.prepared ≤ Usize.max; exact preparedBound) (by simp)
    (by simpa using globalCapacity) (decodeStore view code before) initialModule storeWf frameWf context
    before.globals.val (by intro _; exact ⟨[], by simp [published, preparedGlobals], .nil⟩)
  change runtime.store.instantiate.Store.instantiate_inner_loop7 memory hooks floats allocator
    {trace.prepared with instances := trace.publishedInstances} platform (.Ok ()) 0#usize before.instances.len
    ⦃ _ ⦄ at result
  rw [trace.globalRun] at result
  simp only [WP.spec_ok] at result
  obtain ⟨after, status, equal, staged, objectBound, accounting, metadata, next, nextFound, nextSource,
    bindings, imports, segments, elements, datas, elementMap, dataMap, sourceContext, values⟩ := result
  obtain ⟨rfl, _, rfl⟩ := (storeParts_inj _ _ _ _ _ _).mp equal
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

theorem PreparedRun.global_source_values {M P F A : Type}
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
    ∃ produced, trace.globalStore.globals.val = before.globals.val ++ produced ∧
      GlobalSourceValues (decodeStore view code before) initialModule module.module.env.globals.val produced := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, produced, stored, evaluated⟩ :=
    trace.global_source_context laws law shape accounted cache valid compiled code initialModule
      functionMap globalMap storeWf frameWf
  exact ⟨produced, stored, evaluated⟩
end Exec.Store
