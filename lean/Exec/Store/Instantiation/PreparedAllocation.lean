import Exec.Store.Instantiation.PreparedAllocationContent
import Exec.Store.Instantiation.PreparedExternalMaps
import Exec.Store.Invariant.SourceExports
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- The source initializer frame contains imported globals and the complete
function address map, before any defined global or segment is allocated. -/
def allocationInitial {M : Type} (raw : ModuleBinary.Module) (before : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) : moduleinst :=
  ⟨raw.types.map EnvTranslation.funcType,
    seed.funcs.val.map (fun address => address.index.val) ++ List.range' before.funcs.length raw.functions.length,
    seed.globals.val.map (fun address => address.index.val), [], [], [], [], []⟩

theorem allocationInitial_wf {M : Type} (raw : ModuleBinary.Module) (before : runtime.store.Store M)
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
    (valid : ModuleEnv.Valid module.module.env module.profile) (compiled : Code.InitializerMappings module)
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
        (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready,
          decodeInstance ready next) := by
  have storeWf := decodeStore_wf view code before shape oldSyntax
  have frameWf : wf_frame ⟨[], allocationInitial raw before trace.seed⟩ := by
    constructor
    · simp [Forall]
    · exact allocationInitial_wf raw before trace.seed
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
  have instWf := decodeInstance_wf _ _ ready next sourceSyntax
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
    exact .globalinst_case_ _ _ (decodeWords_wf _ _ _)
  have datasWf : Forall wf_datainst (module.module.tail.data.val.map sourceDataPayload) := by
    intro value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact .datainst_case_ _ (decodeBytes_wf original.init.val)
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
