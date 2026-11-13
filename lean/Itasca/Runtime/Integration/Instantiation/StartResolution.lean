import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.Interp.Relations.SyntheticInitializerCauses
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Store.Invariant.OwnedInitializerErrors
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.FunctionTypingExtension
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Compiler.Module.SchedulerCapacities
import Itasca.Runtime.Store.Instantiation.NoStart
import Itasca.Runtime.Store.Instantiation.Linked
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Integration.Execution.MemoryInit
import Itasca.Runtime.Store.Invariant.FunctionStagingCauses
import Itasca.Runtime.Compiler.Module.CompileDataCount
import Itasca.Runtime.Integration.Api.InvocationEntryResources
import Itasca.Runtime.SourceMachine.Sim.Structured

/-!
Sections, each formerly its own module: InstantiateSourceOrigin, PreparedCertifiedExecutable, PreparedCertifiedExecutableApi, StartAmbient, StartResolution.
-/

/-! ## InstantiateSourceOrigin -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca Store

/-- The generated instantiation configuration at the actual publication
cutpoint: source element/data initialization followed by the optional start. -/
def sourceInstantiationConfiguration {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (raw : ModuleBinary.Module) : config :=
  ⟨⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩,
    (Spec.Segment.elementPrograms (raw.elements.map ModuleElaboration.element)).flatten.map admininstr_instr ++
    ((Spec.Segment.dataPrograms (raw.data.map ModuleData.translate)).flatten.map admininstr_instr ++
      (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩

end Itasca.Runtime.Integration

end

/-! ## PreparedCertifiedExecutable -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca Store

/-- The actual preparation trace constructs source typing and retained compiler
certificates for the fresh store, including all old functions and instances. -/
theorem prepared_certified_executable {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (oldCode : CodeInterpretation) (old : CertifiedSupportedStore view oldCode before)
    (accounted : SegmentAccounting before)
    {tables memories} (cache : ModuleEnv.Cache module.module.env tables memories)
    (valid : ModuleEnv.Valid module.module.env)
    (initializers : Compiler.InitializerMappings module)
    (raw : ModuleBinary.Module)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    {bytes}
    (encoded : ModuleBinary.ModuleEncodingWith Profile.CodeEncoding raw bytes)
    (functions : Compiler.ExecutableModuleFunctions module (Compiler.sourceFunctions raw))
    (dataCount : ∀ count, module.module.env.data_count = some count →
      count.val = module.module.tail.data.val.length)
    (bounds : SegmentBounds ready) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedSupportedStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      SourceMachine.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready)
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
  have sourceSyntax : StoreSyntax (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) trace.dataStore := by
    apply old.storeSyntax.staged (install_code_agrees before oldCode (Compiler.sourceFunctions raw)) retained
    · simpa only [trace.committed] using Nat.le_of_eq count
    · intro actual lookup
      have equal : actual = inst := Option.some.inj (lookup.symm.trans found)
      subst actual
      exact instance_syntax_source oldCode before.instances.length inst raw elaborated typed instMatched
  have readySyntax : StoreSyntax (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready :=
    sourceSyntax.instances_eq (by simp only [trace.committed])
  have readySegments : SegmentTypeBindings ready inst := by
    constructor
    · simpa only [trace.committed] using segments.tables
    · simpa only [trace.committed] using segments.elements
  have bindings := module_bindings_source view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw))
    ready inst raw instMatched shaped readySyntax (shaped.instances inst (List.mem_of_getElem? readyFound)) bounds
    code.type_entries code.function_table (by simpa only [source] using globals) tableMap memoryMap readySegments
  refine ⟨inst, readyFound, source, ?_, ?_, bindings⟩
  · refine ⟨shaped, readySyntax, ?_, ?_, ?_, bounds⟩
    · exact code.core_typed oldCode raw old.shape old.storeSyntax old.typed
        (decode_store_wf view _ ready shaped readySyntax) readyFound elaborated typed instMatched bindings
    · exact code.source_executable oldCode raw old.shape old.supported readyFound elaborated instMatched encoded
    · exact code.executable_compiled oldCode old.shape old.compiled readyFound (Compiler.sourceFunctions raw)
        (by simpa only [source] using functions) (by simpa only [source] using dataCount) (by simpa only [source] using cache)
  · exact counted.preserve (by simp only [trace.committed]) (by simp only [trace.committed]) (by simp only [trace.committed])
end Itasca.Runtime.Integration

end

/-! ## PreparedCertifiedExecutableApi -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca Store

/-- The actual preparation trace constructs source typing and retained compiler
certificates for the fresh store, including all old functions and instances. -/
theorem prepared_certified_executable_api {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {before : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {platform : P} {ready : runtime.store.Store M}
    (trace : PreparedRun memory hooks floats allocator view before module platform ready)
    (laws : Platform.MemoryLaws memory view) (law : Platform.AllocCorrect allocator)
    (oldCode : CodeInterpretation) (old : CertifiedExecutableApiStore view oldCode before)
    (accounted : SegmentAccounting before)
    {tables memories} (cache : ModuleEnv.Cache module.module.env tables memories)
    (valid : ModuleEnv.Valid module.module.env)
    (initializers : Compiler.InitializerMappings module)
    (raw : ModuleBinary.Module)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    {bytes}
    (encoded : ModuleBinary.ModuleEncodingWith Profile.CodeEncoding raw bytes)
    (functions : Compiler.ExecutableModuleFunctions module (Compiler.sourceFunctions raw))
    (dataCount : ∀ count, module.module.env.data_count = some count →
      count.val = module.module.tail.data.val.length)
    (bounds : SegmentBounds ready) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedExecutableApiStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      SourceMachine.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready)
        (decodeInstance ready inst) (ModuleElaboration.contextOf raw) := by
  obtain ⟨inst,found,source,certified,counted,bindings⟩ :=
    prepared_certified_executable trace laws law oldCode old.toCertifiedSupportedStore accounted
      cache valid initializers raw elaborated typed matched encoded functions dataCount bounds
  exact ⟨inst,found,source,⟨certified,trace.export_bounds laws law old.shape accounted cache valid initializers old.exportBounds⟩,
    counted,bindings⟩
end Itasca.Runtime.Integration

end

/-! ## StartAmbient -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

def ambientStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr) : config :=
  ⟨⟨Store.decodeStore view code store, ambient⟩, [.CALL_ADDR address.index.val]⟩

end Itasca.Runtime.Integration

end

/-! ## StartResolution -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

/-- Module-start execution uses the newly installed module and no ambient locals. -/
def moduleStartFrame {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) : frame :=
  ⟨[], Store.decodeInstance store inst⟩

def moduleStartConfiguration {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) : config :=
  ⟨⟨Store.decodeStore view code store, moduleStartFrame store inst⟩, [.CALL (.mk_uN index.val)]⟩

theorem module_start_frame_wf {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (index : Usize) (inst : runtime.store.ModuleInst)
    (sourceSyntax : Store.StoreSyntax code store) (found : store.instances.val[index.val]? = some inst) :
    wf_frame (moduleStartFrame store inst) := by
  apply wf_frame.frame_case_
  · simp [Forall]
  · exact Store.decode_instance_wf code index.val store inst (sourceSyntax index.val inst found)

theorem module_start_resolve {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) (address : runtime.FuncAddr)
    (storeWf : wf_store (Store.decodeStore view code store))
    (frameWf : wf_frame (moduleStartFrame store inst))
    (mapped : inst.funcs.val[index.val]? = some address) :
    StepH (moduleStartConfiguration view code store inst index) []
      (ambientStartConfiguration view code store (moduleStartFrame store inst) address) := by
  apply SourceMachine.call_resolve _ _ index.val address.index.val storeWf frameWf
  · simp only [moduleStartFrame, Store.decodeInstance, List.getElem?_map, mapped, Option.map_some]
  · scalar_tac

end Itasca.Runtime.Integration

end
