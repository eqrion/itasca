import Exec.Store.Instantiation.PreparedAllocation
import Exec.Code.Module.SourceInstantiation
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
    (valid : ModuleEnv.Valid module.module.env module.profile) (compiled : Code.InitializerMappings module)
    (code : CodeInterpretation) (oldSyntax : StoreSyntax code before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    ∃ next, ready.instances.val[before.instances.len.val]? = some next ∧ next.module = module ∧
      fun_instantiate (decodeStore view code before) (ModuleElaboration.moduleOf raw) (imports.val.map decodeExternal)
        ⟨⟨decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready,
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
  apply Code.source_instantiate encoded elaborated typed (decodeStore view code before)
    (decodeStore view (installCode code before.instances.len.val (Code.sourceFunctions raw)) ready)
    (imports.val.map decodeExternal) (decodeInstance ready next) (allocationInitial raw before trace.seed)
    (trace.seed.funcs.val.map fun address => address.index.val) (trace.seed.globals.val.map fun address => address.index.val)
    ((globals.map decodeGlobal).map globalinst.VALUE) ((elements.map decodeElement).map eleminst.REFS)
    importFunctions importGlobals ?_ ?_ ?_ allocated (decodeStore_wf view code before shape oldSyntax)
  · simp only [allocationInitial, decodeStore, List.length_map, List.length_zipWith, elaborated.code_count,
      Nat.min_self, List.range'_eq_map_range]
  · simpa only [rawGlobals] using globalValues.raw_evaluations
  · simpa only [rawElements] using elementValues.raw_evaluations
end Itasca.Runtime.Store
