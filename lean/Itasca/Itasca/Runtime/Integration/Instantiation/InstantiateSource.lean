import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.Interp.Calls.OutcomesAndResolution
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.StateAndOwnership
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.SourceMachine.EntryAndBranchTables
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Interp.Machine.Progress.UnreachableExecution
import Itasca.Runtime.Interp.Relations.EntryEffects
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Instantiation.PreparedRunTableMemory
import Itasca.Runtime.Store.Invariant.CoreInstantiationSource
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Compiler.Local.Source.ModuleSourceAndSubmission
import Itasca.Runtime.Store.Initialization.SegmentSourceStaging
import Itasca.Runtime.Compiler.Module.Compilation
import Itasca.Runtime.Store.Instantiation.NoStart
import Itasca.Runtime.Store.Instantiation.Linked
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Integration.Execution.MemoryOperations
import Itasca.Runtime.Store.Invariant.FunctionAndTypeStagingCauses
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions
import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.SourceMachine.Core.OperationsAndMemoryTyping
import Itasca.Runtime.SourceMachine.OwnershipExtension
import Itasca.Runtime.Interp.Relations.SourceCallCause
import Itasca.Runtime.Interp.State.ObjectBindingsAndMutation
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.Relations.NormalizationAndValueTypes
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Core.ProgressAndBounds
import Itasca.Runtime.Interp.Numeric.Integer.ConversionsAndBinaryContracts
import Itasca.Runtime.Interp.Numeric.Integer.SignedOperationsAndCounts
import Itasca.Runtime.SourceMachine.Numeric.TransitionSimulation
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Frames.FrameAndReturnStacks
import Itasca.Runtime.Interp.Control.BrTableSource
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.ScalarExecution
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Machine.Constants.EncodingAndFloat
import Itasca.Runtime.Interp.State.GlobalOperations
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Interp.Machine.Select.Operands
import Itasca.Runtime.Interp.Memory.EncodingAndDispatch
import Itasca.Runtime.Interp.Memory.MemoryEffects
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Store.Invariant.SemanticApi
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Integration.Execution.Mutation.BulkResult
import Itasca.Runtime.Store.Initialization.InitializerResourceCauses
import Itasca.Runtime.Store.Invariant.Rollback
import Itasca.Runtime.Compiler.Local.Initializer

open WebAssembly

/-!
Proofs for Runtime / Integration / Instantiation.

This module collects StartResolution, InstantiateSource.
Each section documents its contracts and consumers.
-/

/-! ## StartResolution -/

section

open Itasca.Representation

/-! ## PreparedCertifiedExecutable -/

section

namespace Itasca.Integration
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
    {tables memories} (cache : Module.Environment.Cache module.module.env tables memories)
    (valid : Module.Environment.Valid module.module.env)
    (initializers : Compiler.InitializerMappings module)
    (raw : Binary.Module)
    (elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (matched : Module.Elaboration.Matches module.module.env module.module.tail raw)
    {bytes}
    (encoded : Binary.ModuleEncodingWith CodeEntry.CodeEncoding raw bytes)
    (functions : Compiler.ExecutableModuleFunctions module (Compiler.sourceFunctions raw))
    (dataCount : ∀ count, module.module.env.data_count = some count →
      count.val = module.module.tail.data.val.length)
    (bounds : SegmentBounds ready) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedSupportedStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      SourceMachine.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready)
        (decodeInstance ready inst) (Module.Elaboration.contextOf raw) := by
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
  have instMatched : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw := by
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
end Itasca.Integration

end

/-! ## PreparedCertifiedExecutableApi -/

section

namespace Itasca.Integration
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
    (oldCode : CodeInterpretation) (old : CertifiedApiStore view oldCode before)
    (accounted : SegmentAccounting before)
    {tables memories} (cache : Module.Environment.Cache module.module.env tables memories)
    (valid : Module.Environment.Valid module.module.env)
    (initializers : Compiler.InitializerMappings module)
    (raw : Binary.Module)
    (elaborated : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (matched : Module.Elaboration.Matches module.module.env module.module.tail raw)
    {bytes}
    (encoded : Binary.ModuleEncodingWith CodeEntry.CodeEncoding raw bytes)
    (functions : Compiler.ExecutableModuleFunctions module (Compiler.sourceFunctions raw))
    (dataCount : ∀ count, module.module.env.data_count = some count →
      count.val = module.module.tail.data.val.length)
    (bounds : SegmentBounds ready) :
    ∃ inst, ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
      CertifiedApiStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready ∧
      SegmentAccounting ready ∧
      SourceMachine.ModuleBindings (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) ready)
        (decodeInstance ready inst) (Module.Elaboration.contextOf raw) := by
  obtain ⟨inst,found,source,certified,counted,bindings⟩ :=
    prepared_certified_executable trace laws law oldCode old.toCertifiedSupportedStore accounted
      cache valid initializers raw elaborated typed matched encoded functions dataCount bounds
  exact ⟨inst,found,source,⟨certified,trace.export_bounds laws law old.shape accounted cache valid initializers old.exportBounds⟩,
    counted,bindings⟩
end Itasca.Integration

end

/-! ## StartAmbient -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly

def ambientStartConfiguration {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr) : config :=
  ⟨⟨Representation.decodeStore view code store, ambient⟩, [.CALL_ADDR address.index.val]⟩

end Itasca.Integration

end

/-! ## StartResolution -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std WebAssembly

def moduleStartConfiguration {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) : config :=
  ⟨⟨Representation.decodeStore view code store, moduleStartFrame store inst⟩, [.CALL (.mk_uN index.val)]⟩

theorem module_start_frame_wf {M : Type} (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (index : Usize) (inst : runtime.store.ModuleInst)
    (sourceSyntax : Store.StoreSyntax code store) (found : store.instances.val[index.val]? = some inst) :
    wf_frame (moduleStartFrame store inst) := by
  apply wf_frame.frame_case_
  · simp [Forall]
  · exact Store.decode_instance_wf code index.val store inst (sourceSyntax index.val inst found)

theorem module_start_resolve {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : U32) (address : runtime.FuncAddr)
    (storeWf : wf_store (Representation.decodeStore view code store))
    (frameWf : wf_frame (moduleStartFrame store inst))
    (mapped : inst.funcs.val[index.val]? = some address) :
    StepH (moduleStartConfiguration view code store inst index) []
      (ambientStartConfiguration view code store (moduleStartFrame store inst) address) := by
  apply SourceMachine.call_resolve _ _ index.val address.index.val storeWf frameWf
  · simp only [moduleStartFrame, Representation.decodeInstance, List.getElem?_map, mapped, Option.map_some]
  · scalar_tac

end Itasca.Integration

end

end

/-! ## InstantiateSource -/

section

open Itasca.Representation

/-! ## InstantiateExecutableEventfulOrigin -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca Store

/-- Actual accepted compilation and instantiation either retain a rollback
prefix or reach a certified store that is exactly the generated source
instantiation result. No allocation, initializer, or compiler correctness
certificate is supplied by the caller. -/
theorem instantiate_compiled_executable_eventful_origin {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (code : CodeInterpretation) (certified : CertifiedApiStore view code before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module)) :
    ∃ raw, Binary.ModuleEncodingWith CodeEntry.CodeEncoding raw bytes.val ∧
      Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw) ∧
      Module.Elaboration.Matches module.module.env module.module.tail raw ∧
      Module_ok (Module.Elaboration.moduleOf raw) ∧
      ((∃ error staged,
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
          .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
       ∃ ready inst,
        ready.instances.val[before.instances.len.val]? = some inst ∧ inst.module = module ∧
        CertifiedApiStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready ∧
        (FunctionCapacities code before → FunctionCapacities
          (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready) ∧
        SegmentAccounting ready ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧
        Representation.FunctionTable ready inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType) ∧
        fun_instantiate (decodeStore view code before) (Module.Elaboration.moduleOf raw) (imports.val.map decodeExternal)
          (sourceInstantiationConfiguration view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready inst raw) ∧
        Extend_store (decodeStore view code before)
          (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready) ∧
        Store.MetadataExtended before ready ∧
        runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
          runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false) := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, functions, initializers⟩ :=
    Compiler.compile_executable_functions allocator law bytes limits module accepted
  obtain ⟨capacityRaw,capacityEncoded,_,_,_,_,_,capacities⟩ :=
    Compiler.compile_executable_capacities allocator law bytes limits module accepted
  have sameRaw := Binary.module_unique encoded capacityEncoded
  subst capacityRaw
  refine ⟨raw, encoded, elaborated, matched, typed, ?_⟩
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits module accepted
  have valid : Module.Environment.Valid module.module.env := by
    exact (witness.semantic law).1
  have decomposition := instantiate_compiled_linked_bounded_decomposition memory hooks floats allocator law view laws
    before module imports platform certified.shape accounted certified.segmentBounds bytes limits accepted handles
  rcases decomposition with rejected | ⟨ready, inst, shape, found, source, initializersReady, types, counts, metadata, bounded, ⟨trace⟩, continued⟩
  · exact Or.inl rejected
  · obtain ⟨certifiedInst, certifiedFound, certifiedSource, readyCertified, readyAccounting, bindings⟩ :=
      prepared_certified_executable_api trace.toPreparedRun laws law code certified accounted matched.2 valid initializers
        raw elaborated typed matched encoded functions (witness.data_count law) bounded
    have same : certifiedInst = inst := Option.some.inj (certifiedFound.symm.trans found)
    subst certifiedInst
    obtain ⟨sourceInst, sourceFound, sourceModule, instantiated⟩ := trace.source_instantiation laws law
      certified.shape accounted raw matched.2 matched elaborated typed encoded valid initializers code certified.storeSyntax handles
    have sameSource : sourceInst = inst := Option.some.inj (sourceFound.symm.trans found)
    subst sourceInst
    obtain ⟨_,_,_,_,_,retained,_,_⟩ := trace.toPreparedRun.shape_data laws law certified.shape accounted matched.2 valid initializers
    obtain ⟨hfuncs,hglobals,htables,hmems,helems,hdatas⟩ := decode_store_prefix view
      (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) before trace.toPreparedRun.dataStore certified.shape retained
    have decodedReady : decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready =
        decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) trace.toPreparedRun.dataStore := by
      refine (congrArg (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw))) trace.toPreparedRun.committed).trans ?_
      unfold decodeStore
      congr 1
    have agrees : decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) before = decodeStore view code before := by
      simpa only [alloc.vec.Vec.len_val] using decode_store_code_agrees view (install_code_agrees before code (Compiler.sourceFunctions raw))
    have extension : Extend_store (decodeStore view code before)
        (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready) := by
      have result := store_prefix_extends
        (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) before)
        (decodeStore view (installCode code before.instances.len.val (Compiler.sourceFunctions raw)) ready)
        (by rw [agrees]; exact decode_store_wf view code before certified.shape certified.storeSyntax)
        (decode_store_wf view _ ready readyCertified.shape readyCertified.storeSyntax)
        (by simpa only [decodedReady] using hfuncs) (by simpa only [decodedReady] using hglobals)
        (by simpa only [decodedReady] using htables) (by simpa only [decodedReady] using hmems)
        (by simpa only [decodedReady] using helems) (by simpa only [decodedReady] using hdatas)
      simpa only [agrees] using result
    refine Or.inr ⟨ready, inst, found, source, readyCertified, ?_, readyAccounting, initializersReady,
      types, metadata.function_table, instantiated, extension, ?_, continued⟩
    · intro oldCapacities
      exact metadata.capacities code oldCapacities found (Compiler.sourceFunctions raw)
        (by simpa only [source] using capacities) (by simpa only [source] using matched.2)
    · rw [trace.toPreparedRun.committed]
      exact ⟨retained.identity,retained.funcs,retained.types,retained.instances⟩
end Itasca.Integration

end

/-! ## InstantiateSource -/

section

/-! Public instantiation links, allocates and initializes a module and returns its start
function without running it. The construction is total and uses no host callback. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca Store WebAssembly

/-- Publication runs the segment initializer and resolves the start function. -/
theorem commit_instance_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits=.ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]?=some inst)
    (code : CodeInterpretation) (certified : ExecutableInv view code store)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType))
    (raw : Binary.Module)
    (matched : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (initialWf : wf_config (sourceInstantiationConfiguration view code store inst raw)) :
    runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false
      ⦃ out => out.2.2.1=platform ∧ out.2.2.2=true ∧ ExecutableInv view code out.2.1 ∧
        Extend_store (decodeStore view code store) (decodeStore view code out.2.1) ∧
        Store.MetadataExtended store out.2.1 ∧
        (∀ instantiated,out.1=.Ok instantiated →
          instantiated.instance=identity ∧ StartResolved out.2.1 inst instantiated.start) ∧
        InitializedSource (sourceInstantiationConfiguration view code store inst raw)
          (decodeStore view code out.2.1) (moduleStartFrame out.2.1 inst) out.1 ∧
        ∀ error,out.1=.Err error → (error=.Trap .MemoryOutOfBounds ∨ error=.Trap .TableOutOfBounds) ∨
          (out.2.1=store ∧ SegmentSetupCause allocator store inst.module error) ⦄ := by
  have bindings := certified.shape.initializer_bindings (List.mem_of_getElem? found)
  obtain ⟨witness⟩ := Compiler.compile_accepted allocator bytes limits inst.module accepted
  have valid : Itasca.Module.Environment.Valid inst.module.module.env := by
    exact (witness.semantic law).1
  let continuation := (inst.module.module.env.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList
  have continuationWf : Forall wf_admininstr continuation := by
    cases hs : inst.module.module.env.start with
    | none => simp [continuation,hs,Forall]
    | some index =>
      have indexWf : wf_uN 32 (.mk_uN index.val) := by constructor; scalar_tac
      simpa [continuation,hs,Forall] using wf_admininstr.admininstr_case_10 (.mk_uN index.val) indexWf
  have startEq : raw.start = inst.module.module.env.start := congrArg Binary.Module.start matched.1
  have initSource := initialize_segments_raw_source_causes memory hooks floats allocator view laws law store platform identity.index
    inst bytes limits accepted found code certified.shape certified.storeSyntax certified.segmentBounds
    imports bindings types (moduleStartFrame store inst)
    (module_start_frame_wf code store identity.index inst certified.storeSyntax found) rfl raw matched continuation continuationWf
  obtain ⟨⟨status,initialized,host⟩,initRun,fresh,extension,metadata,hostEq⟩ :=
    WP.spec_imp_exists (initialize_segments_certified_supported memory hooks floats allocator view laws law
      store platform identity.index inst bytes limits accepted found code certified.toCertifiedSupportedStore
      imports bindings types)
  dsimp only at fresh extension metadata hostEq
  subst host
  rw [initRun,WP.spec_ok] at initSource
  dsimp only at initSource
  have frameMetadata : Store.MetadataPreserved store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  have initializedInv : ExecutableInv view code initialized :=
    ⟨⟨fresh,certified.exportBounds.instances_eq metadata.space.instances⟩,
      ⟨by simpa only [metadata.space.elements,metadata.space.instances] using certified.segmentAccounting.elements,
       by simpa only [metadata.space.datas,metadata.space.instances] using certified.segmentAccounting.datas⟩,
      certified.capacities.metadata metadata.space.functions metadata.space.instances metadata.space.signatures metadata.space.identity⟩
  have frameEq : moduleStartFrame store inst = moduleStartFrame initialized inst := by
    simp only [moduleStartFrame,decodeInstance,metadata.space.signatures]
  have sourceEq : (⟨⟨decodeStore view code store,moduleStartFrame store inst⟩,
      segmentRawSource raw ++ continuation⟩ : config) = sourceInstantiationConfiguration view code store inst raw := by
    simp only [sourceInstantiationConfiguration,segmentRawSource,continuation,startEq,moduleStartFrame,List.append_assoc]
  cases status with
  | Err error =>
    have run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
        .ok (.Err error,initialized,platform,true) := by
      simp [runtime.store.instantiate.Store.commit_instance,initRun,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]
    rw [run,WP.spec_ok]
    refine ⟨rfl,rfl,initializedInv,extension,frameMetadata.prefix,(by intro _ impossible; cases impossible),?_,?_⟩
    · rcases initSource with ⟨reason,statusEq,unchanged,_⟩ | ⟨classified,reduced⟩
      · cases statusEq
        subst initialized
        exact ⟨_,StepsH.refl initialWf⟩
      · rw [sourceEq,frameEq] at reduced
        change error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds at classified
        rcases classified with rfl | rfl <;> exact reduced
    · intro reported same
      cases same
      rcases initSource with ⟨reason,statusEq,unchanged,cause⟩ | ⟨classified,_⟩
      · cases statusEq
        exact Or.inr ⟨unchanged,cause⟩
      · exact Or.inl classified
  | Ok value =>
    cases value
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    obtain ⟨actual,read,same⟩ := WP.spec_imp_exists (Interp.vec_index_given initialized.instances identity.index inst afterFound)
    subst actual
    have reduced : StepsH (sourceInstantiationConfiguration view code store inst raw) []
        ⟨⟨decodeStore view code initialized,moduleStartFrame initialized inst⟩,continuation⟩ := by
      rcases initSource with ⟨reason,impossible,_,_⟩ | ⟨_,reduced⟩
      · cases impossible
      · rw [sourceEq,frameEq] at reduced
        simpa only [segmentAfter] using reduced
    cases start : inst.module.module.env.start with
    | none =>
      have run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
          .ok (.Ok ⟨identity,none⟩,initialized,platform,true) := by
        simp [runtime.store.instantiate.Store.commit_instance,initRun,core.result.Result.Insts.CoreOpsTry.branch,
          alloc.vec.Vec.index_slice_index,read,runtime.compiler.ExecutableModule.env.eq,
          Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.start,start]
      rw [run,WP.spec_ok]
      refine ⟨rfl,rfl,initializedInv,extension,frameMetadata.prefix,?_,?_,(by intro _ impossible; cases impossible)⟩
      · intro instantiated same
        cases same
        exact ⟨rfl,start⟩
      · simpa only [InitializedSource,continuation,start,Option.map_none,Option.toList_none,List.map_nil] using reduced
    | some index =>
      obtain ⟨address,function,signature,mapped,owner,hf,hs,params,results⟩ :=
        Store.start_function_resolves (metadata.space.function_table table) valid index start
      let slot := UScalar.cast .Usize index
      have mappedSlot : inst.funcs.val[slot.val]? = some address := by simpa [slot] using mapped
      obtain ⟨actual,addressRun,same⟩ := WP.spec_imp_exists (Interp.vec_index_given inst.funcs slot address mappedSlot)
      subst actual
      dsimp only [slot] at addressRun
      have run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
          .ok (.Ok ⟨identity,some address⟩,initialized,platform,true) := by
        simp only [runtime.store.instantiate.Store.commit_instance,initRun,lift,bind_ok,uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry.branch,runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.start,
          alloc.vec.Vec.index_slice_index,read,start,addressRun]
      rw [run,WP.spec_ok]
      refine ⟨rfl,rfl,initializedInv,extension,frameMetadata.prefix,?_,?_,(by intro _ impossible; cases impossible)⟩
      · intro instantiated same
        cases same
        exact ⟨rfl,index,start,mapped,owner,(List.getElem?_eq_some_iff.mp hf).1⟩
      · have call := module_start_resolve view code initialized inst index address initializedInv.well_formed
          (module_start_frame_wf code initialized identity.index inst initializedInv.storeSyntax afterFound) mapped
        have prefixSteps : StepsH (sourceInstantiationConfiguration view code store inst raw) []
            (moduleStartConfiguration view code initialized inst index) := by
          simpa only [continuation,start,Option.map_some,Option.toList_some,moduleStartConfiguration] using reduced
        simpa only [InitializedSource,ambientStartConfiguration,List.nil_append,Option.toList_some,
          List.map_cons,List.map_nil] using Spec.steps_h_trans prefixSteps (Spec.steps_h_single call)

/-- Accepted compilation and public instantiation, with the code interpretation that installs the
new module's source functions. -/
theorem instantiate_compiled_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
    (raw : Binary.Module)
    (encoded : WebAssembly.Binary.ModuleEncoding (Binary.Source.rawModule raw) (Binary.Source.bytes bytes.val)) :
    Module_ok (Module.Elaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ (result, after, nextPlatform) => ExecutableInv view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after ∧
          Store.MetadataExtended before after ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after) ∧
          InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Compiler.sourceFunctions raw))
            before module imports raw platform result after nextPlatform ∧
          ∀ error,result=.Err error → InstantiationResourceCause memory hooks floats allocator
            view oldCode before module imports platform raw after error ⦄ := by
  obtain ⟨actualRaw,actualEncoded,elaborated,matched,typed,origin⟩ :=
    instantiate_compiled_executable_eventful_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old.toCertifiedApiStore old.segmentAccounting handles bytes limits accepted
  have sameRaw := Binary.Source.rawModuleInjective (WebAssembly.Binary.ModuleEncoding.unique encoded
    (Binary.Source.moduleEncoding actualEncoded))
  subst actualRaw
  refine ⟨typed,?_⟩
  rcases origin with ⟨error,staged,returned,retained⟩ |
    ⟨ready,inst,found,source,readyCertified,readyCapacities,readyAccounting,initializers,types,table,allocated,
      preparedExtension,preparedPrefix,continued⟩
  · obtain ⟨cause,_,_,_⟩ := instantiate_compiled_precommit_origins memory hooks floats allocator law view laws
      before module imports platform old.shape old.segmentAccounting bytes limits accepted handles
      error staged platform returned
    obtain ⟨_,_,evidence⟩ := instantiate_compiled_precommit_resource_causes memory hooks floats allocator law view laws
      before module imports platform old.shape old.segmentAccounting bytes limits accepted handles error staged platform returned
    obtain ⟨⟨result,after,nextPlatform⟩,run,resultEq,storeEq,hostEq⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run,WP.spec_ok]
    have rollbackInv : ExecutableInv view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) before :=
      ⟨old.toCertifiedApiStore.install_code (Compiler.sourceFunctions raw),old.segmentAccounting,
        old.capacities.code_agrees (install_code_agrees before oldCode (Compiler.sourceFunctions raw))⟩
    have rollbackExtension : Extend_store (decodeStore view oldCode before)
        (decodeStore view (installCode oldCode before.instances.length (Compiler.sourceFunctions raw)) after) := by
      rw [storeEq,decode_store_code_agrees view (install_code_agrees before oldCode (Compiler.sourceFunctions raw))]
      exact Spec.extend_store_refl _ old.well_formed
    refine ⟨(by simpa only [storeEq] using rollbackInv),(by simpa only [storeEq] using Store.MetadataExtended.refl before),
      rollbackExtension,Or.inl ⟨error,resultEq,cause,storeEq,hostEq⟩,?_⟩
    · intro failed rejected
      have same : error = failed := core.result.Result.Err.inj (resultEq.symm.trans rejected)
      subst failed
      cases error <;> try trivial
      · exact Or.inl ⟨storeEq,_,rfl,staged,returned,evidence⟩
  · have initialWf : wf_config (sourceInstantiationConfiguration view
        (installCode oldCode before.instances.len.val (Compiler.sourceFunctions raw)) ready inst raw) := by
      have wf : ∀ s m xs c, fun_instantiate s m xs c → wf_config c := by
        intro s m xs c h
        cases h
        assumption
      exact wf _ _ _ _ allocated
    have acceptedInst : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : Module.Elaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    have tail := commit_instance_source memory hooks floats allocator view laws law ready platform
      ⟨before.id,before.instances.len⟩ inst bytes limits acceptedInst found
      (installCode oldCode before.instances.length (Compiler.sourceFunctions raw))
      ⟨readyCertified,readyAccounting,readyCapacities old.capacities⟩ initializers types table raw matchedInst initialWf
    unfold runtime.store.instantiate.Store.instantiate_with
    rw [←continued]
    apply WP.spec_bind tail
    rintro ⟨result,after,host,committed⟩ ⟨hostEq,commit,valid,tailExtension,retained,success,initializedSource,causes⟩
    dsimp only at hostEq commit valid tailExtension retained success initializedSource causes ⊢
    subst committed host
    have outcome : InstantiationSourceOutcome view oldCode (installCode oldCode before.instances.length (Compiler.sourceFunctions raw))
        before module imports raw platform result after platform :=
      Or.inr ⟨inst,_,retained.instance_lookup found,source,rfl,allocated,initializedSource,success⟩
    cases result with
    | Ok instantiated =>
      simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,Bool.false_eq_true,↓reduceIte,WP.spec_ok]
      exact ⟨valid,preparedPrefix.trans retained,Spec.extend_store_trans preparedExtension tailExtension,outcome,
        fun _ impossible => by cases impossible⟩
    | Err error =>
      simp only [uncurry_apply_pair,runtime.store.instantiation_failed,bind_ok,↓reduceIte,WP.spec_ok]
      refine ⟨valid,preparedPrefix.trans retained,Spec.extend_store_trans preparedExtension tailExtension,outcome,?_⟩
      intro failed rejected
      cases rejected
      cases error <;> try trivial
      all_goals
        rcases causes _ rfl with trap | ⟨unchanged,setup⟩
        · rcases trap with impossible | impossible <;> cases impossible
        · exact Or.inr ⟨ready,inst,found,source,allocated,continued,unchanged,setup⟩

end Itasca.Integration

end

end
