import Exec.Theorems.Composition.Certified.CertifiedFloatCore
import Exec.Store.Instantiation.PreparedRunShape
import Exec.Store.Instantiation.PreparedRunGlobalTypes
import Exec.Store.Instantiation.PreparedRunTableMemory
import Exec.Store.Instantiation.PreparedRunBounds
import Exec.Store.Invariant.FloatCoreInstantiationSource
import Exec.Store.Invariant.FloatCoreInstantiationCode
import Exec.Code.Module.CompileFloatCore
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store

/-- The actual preparation trace constructs source typing and retained compiler
certificates for the fresh store, including all old functions and instances. -/
theorem prepared_certified_float_core {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (oldCode : CodeInterpretation) (old : CertifiedFloatCoreStore view oldCode before)
    (accounted : SegmentAccounting before)
    {tables memories} (cache : ModuleEnv.Cache module.module.env tables memories)
    (valid : ModuleEnv.Valid module.module.env module.profile)
    (initializers : Code.InitializerMappings module)
    (raw : ModuleBinary.Module)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (supported : Code.ModuleFloatCore raw)
    (functions : Code.FloatCoreModuleFunctions module (Code.sourceFunctions raw))
    (bounds : SegmentBounds ready) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedFloatCoreStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      Abs.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready)
        (decodeInstance ready inst) (ModuleElaboration.contextOf raw) := by
  obtain ⟨inst, found, source, shaped, segments, retained, counted, code⟩ :=
    trace.shape_data laws law old.shape accounted cache valid initializers
  have readyFound : ready.instances.val[before.instances.len.val]? = some inst := by
    simpa only [trace.committed] using found
  obtain ⟨globalInst, globalFound, globalSource, count, globals, elements⟩ :=
    trace.global_types laws law old.shape accounted cache valid initializers
  have equal : globalInst = inst := Option.some.inj (globalFound.symm.trans readyFound)
  subst globalInst
  obtain ⟨mapInst, mapFound, mapSource, tableMap, memoryMap⟩ :=
    trace.table_memory_bindings laws law old.shape accounted cache valid initializers
  have equal : mapInst = inst := Option.some.inj (mapFound.symm.trans readyFound)
  subst mapInst
  have instMatched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
    simpa only [source] using matched
  have sourceSyntax : StoreSyntax (installCode oldCode before.instances.length (Code.sourceFunctions raw)) trace.dataStore := by
    apply old.storeSyntax.staged (installCode_agrees before oldCode (Code.sourceFunctions raw)) retained
    · simpa only [trace.committed] using Nat.le_of_eq count
    · intro actual lookup
      have equal : actual = inst := Option.some.inj (lookup.symm.trans found)
      subst actual
      exact instance_syntax_source oldCode before.instances.length inst raw elaborated typed instMatched
  have readySyntax : StoreSyntax (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready :=
    sourceSyntax.instances_eq (by simp only [trace.committed])
  have readySegments : SegmentTypeBindings ready inst := by
    constructor
    · simpa only [trace.committed] using segments.tables
    · simpa only [trace.committed] using segments.elements
  have bindings := module_bindings_source view (installCode oldCode before.instances.length (Code.sourceFunctions raw))
    ready inst raw instMatched shaped readySyntax (shaped.instances inst (List.mem_of_getElem? readyFound)) bounds
    code.type_entries code.function_table (by simpa only [source] using globals) tableMap memoryMap readySegments
  refine ⟨inst, readyFound, source, ?_, ?_, bindings⟩
  · refine ⟨shaped, readySyntax, ?_, ?_, ?_, bounds⟩
    · exact code.core_typed oldCode raw old.shape old.storeSyntax old.typed
        (decodeStore_wf view _ ready shaped readySyntax) readyFound elaborated typed instMatched bindings
    · exact code.source_float_core oldCode raw old.shape old.core readyFound elaborated instMatched supported
    · exact code.float_core_compiled oldCode old.shape old.compiled readyFound (Code.sourceFunctions raw)
        (by simpa only [source] using functions) (by simpa only [source] using cache)
  · exact counted.preserve (by simp only [trace.committed]) (by simp only [trace.committed]) (by simp only [trace.committed])
/-- Actual successful compilation discharges all source and bytecode
certificates used by preparation. The only source restriction is independently
stated on the encoded module, before compiling it. -/
theorem prepare_compiled_certified_float_core {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (oldCode : CodeInterpretation) (old : CertifiedFloatCoreStore view oldCode before)
    (accounted : SegmentAccounting before)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceFloatCore profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw inst, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleFloatCore raw ∧
      ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedFloatCoreStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      Abs.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) ready)
        (decodeInstance ready inst) (ModuleElaboration.contextOf raw) := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, sliced, functions, initializers, actualProfile⟩ :=
    Code.compile_float_core_functions allocator law bytes profile limits module supported accepted
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  obtain ⟨valid, _⟩ := witness.semantic law
  have actualValid : ModuleEnv.Valid module.module.env module.profile := by
    simpa only [actualProfile] using valid
  have bounds := trace.compiled_segment_bounds laws law old.shape accounted old.segmentBounds bytes profile limits accepted
  obtain ⟨inst, found, source, certified, finalAccounting, bindings⟩ :=
    prepared_certified_float_core trace laws law oldCode old accounted cache actualValid initializers raw
      elaborated typed matched sliced functions bounds
  exact ⟨raw, inst, encoded, typed, sliced, found, source, certified, finalAccounting, bindings⟩
end Exec.Theorems
