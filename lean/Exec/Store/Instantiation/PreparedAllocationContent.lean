import Exec.Store.Instantiation.PreparedSegmentSource
import Exec.Store.Instantiation.PreparedFunctionPayload
import Exec.Store.Instantiation.PreparedRunTableMemoryAllocations
import Exec.Store.Instantiation.PreparedRunShape
import Exec.Store.Invariant.SourceFunctionAllocation
import Exec.Store.Invariant.SourceBindings
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.SourceAllocationLists
import Exec.Spec.AllocationModule
namespace Exec.Store
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
    (valid : ModuleEnv.Valid module.module.env module.profile) (compiled : Code.InitializerMappings module)
    (code : CodeInterpretation) (initialModule : moduleinst)
    (functionMap : initialModule.FUNCS = trace.inst.funcs.val.map (fun address => address.index.val))
    (globalMap : initialModule.GLOBALS = trace.seed.globals.val.map (fun address => address.index.val))
    (storeWf : wf_store (decodeStore view code before)) (frameWf : wf_frame ⟨[], initialModule⟩) :
    ∃ next globals elements,
      ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      GlobalSourceValues (decodeStore view code before) initialModule module.module.env.globals.val globals ∧
      ElementSourceSegments (decodeStore view code before) initialModule module.module.env.elements.val elements ∧
      decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready =
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
      (decodeFunction (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready) =
      before.funcs.val.map (decodeFunction code before) := by
    apply List.map_congr_left
    intro function present
    have retainedFunction := decodeFunction_prefix
      (installCode code before.instances.len.val (Code.sourceFunctions raw)) before trace.dataStore retained view shape function present
    have agrees := decodeFunction_code_agrees (installCode_agrees before code (Code.sourceFunctions raw)) function
    have charge : decodeFunction (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready function =
        decodeFunction (installCode code before.instances.len.val (Code.sourceFunctions raw)) trace.dataStore function := by
      simp only [trace.committed, decodeFunction, decodeInstance]
    exact charge.trans (retainedFunction.trans agrees)
  have functionsStored : ready.funcs.val.map
      (decodeFunction (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready) =
      before.funcs.val.map (decodeFunction code before) ++
      (List.zipWith CodeEntry.function raw.functions raw.codes).map (Spec.allocationFunction (decodeInstance ready next)) := by
    simpa only [metadata.functions, preparedFunctions, typedFunctions, oldFunctions] using allocatedFunctions
  have types := type_entries_decoded codeMetadata.type_entries
  refine ⟨next, globals, elements, found, source, globalValues, elementValues, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dataAddresses⟩
  · unfold decodeStore Spec.allocationStore
    simp only [functionsStored, globalsStored, elementsStored, List.map_append,
      metadata.tables, metadata.memories, tablesStored, memoriesStored, List.map_map, Function.comp_def, datasStored]
  · simpa only [decodeInstance, source, sourceTypes, funext decodeFuncType_source] using types
  · simpa only [metadata.functionMap, preparedFunctionMap, indices] using functionAddresses
  · simpa only [globalValues.length_eq] using globalAddresses
  · simpa only [metadata.tableMap] using tableAddresses
  · simpa only [metadata.memoryMap] using memoryAddresses
  · simpa only [elementValues.length_eq] using elementAddresses
end Exec.Store
