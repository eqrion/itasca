import Itasca.Results.Unique
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions
import Itasca.Runtime.Compiler.Local.Capacity.ConditionalAndSimdAvailability
import Itasca.Module.Elab.ToTyping
import Itasca.Runtime.Compiler.Module.SourceAndSubmission
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Stream.Completeness
import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Relations.Table.PreparedTableInitial
import Itasca.Runtime.Compiler.Body.Relations.ExecutableEmission
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedBodySafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceBudgetAdvance
import Itasca.CodeEntry.Validation
import Itasca.Module.Code.Framing
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryGrowth
import Itasca.Runtime.Compiler.Local.Initializer.ModuleMappings
import Itasca.Module.Const.Parser
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentData
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Stream.RetirementAndFraming
import Itasca.Runtime.Compiler.Local.Source.ModuleSourceAndSubmission
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Body.Reader.Scalar.ScalarEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Local.Lowering.Literal.SourceEffects
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchAndTerminalEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.StackPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Body.ExecutableFunctionCapacity
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryBodyExecutable
import Itasca.Runtime.Compiler.Local.Initializer.LowerContracts
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Module.Env.Externals

open WebAssembly

/-!
Proofs for Runtime / Compiler / Module.

This module collects CompileTotal, PreparationAndGlobalAvailability, CompileExecutable, InitializerCompilationAvailable.
Each section documents its contracts and consumers.
-/

/-! ## CompileTotal -/

section

/-!
# Compile Total

Source initializer bounds and scheduler safety establish normal compiler return. Submission, code-entry and driver cases cover arbitrary inputs, including ordinary Rust errors.
-/

/-! ## InitializerSourceTotal -/

section

/-!
Independent source bounds and normal return of source initializer lowering.
-/

/-! ## Initializer Source Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Binary

/-- The fixed module header fits the compiler's intrinsic input bound. -/
theorem module_header_fits : magicVersion.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  simp only [magicVersion, List.length_cons, List.length_nil, Nat.reduceAdd,
    Itasca.limits.MAX_MODULE_BYTES, UScalar.ofNatCore_val_eq, Nat.reduceLeDiff]

private theorem leb_nonempty {bytes value} (h : Itasca.Binary.Leb128.Encoding bytes value) :
    1 ≤ bytes.length := by
  obtain ⟨before, last, rfl, _⟩ := h
  simp

private theorem rep_count {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (positive : ∀ value bytes, R value bytes → 1 ≤ bytes.length) :
    values.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := positive _ _ hx
    simp only [List.length_cons, List.length_append]
    omega

private theorem vec_count {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) (positive : ∀ value bytes, R value bytes → 1 ≤ bytes.length) :
    values.length + 1 ≤ bytes.length := by
  obtain ⟨count, entries, hc, hr, rfl⟩ := h
  have := leb_nonempty hc
  have := rep_count hr positive
  simp only [List.length_append]
  omega

private theorem element_cost {entry bytes}
    (h : ElementEncoding entry bytes) : entry.init.length + 3 ≤ 3 * bytes.length := by
  obtain ⟨ex, header, init, hh, hi, rfl⟩ := ElementEncoding.reader_parts.mp h
  have := vec_count hi (fun _ _ h => Itasca.Module.Elements.InitializerEncoding.nonempty h)
  simp only [List.length_append]
  omega

private theorem global_cost {entry bytes} (h : GlobalEncoding entry bytes) : 2 ≤ 3 * bytes.length := by
  obtain ⟨ty, expr, ht, _, rfl⟩ := GlobalEncoding.reader_parts.mp h
  obtain rfl := GlobalTypeEncoding.reader_bytes.mp ht
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

private theorem data_cost {entry bytes}
    (h : DataEncoding entry bytes) : 2 ≤ 3 * bytes.length := by
  have := DataEncoding.length_ge_two h
  omega

private theorem rep_cost {α : Type} {R : α → List U8 → Prop} {values bytes}
    (cost : α → Nat) (h : Rep R values bytes)
    (bounded : ∀ value bytes, R value bytes → cost value ≤ 3 * bytes.length) :
    (values.map cost).sum ≤ 3 * bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := bounded _ _ hx
    simp only [List.map_cons, List.sum_cons, List.length_append]
    omega

private theorem padded_cost {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (cost : α → Nat) (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    (bounded : ∀ value bytes, R value bytes → cost value ≤ 3 * bytes.length) :
    (values.map cost).sum ≤ 3 * bytes.length := by
  obtain ⟨customs, sec, _, hs, rfl⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨size, payload, _, ⟨count, entries, _, hr, rfl⟩, rfl⟩ := hp
    have := rep_cost cost hr bounded
    simp only [List.length_append, List.length_cons]
    omega

/-- The independently encoded declaration sections pay for all initializer-map
appends and the defined functions, including empty element segments. -/
theorem initializer_cost_bytes {R raw bytes}
    (encoding : ModuleEncodingWith R raw bytes) :
    raw.functions.length + 2 * raw.globals.length +
      (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length ≤
      3 * bytes.length := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, hf, _, _, hg, _, _, he, _, _, hd, _, rfl, _⟩ := encoding
  have hf := padded_cost (fun _ => 1) hf (fun _ _ h => by have := leb_nonempty h; omega)
  have hg := padded_cost (fun _ => 2) hg (fun _ _ h => global_cost h)
  have he := padded_cost (fun e => e.init.length + 3) he (fun _ _ h => element_cost h)
  have hd := padded_cost (fun _ => 2) hd (fun _ _ h => data_cost h)
  dsimp only [WebAssembly.Binary.SectionField.vector] at hf hg he hd
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at hf hg hd
  simp only [List.length_append]
  omega

/-- Canonical metadata and the fixed module-byte cap discharge both numeric
headroom obligations before initializer lowering runs. No successful initializer
result is assumed. -/
theorem initializer_source_headroom {R raw bytes env tail}
    (encoding : ModuleEncodingWith R raw bytes)
    (matched : Itasca.Module.Elaboration.Matches env tail raw)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    env.func_type_indices.val.length + initializerMappingCost ⟨env, tail⟩ + 1 ≤ Usize.max ∧
    5 * (env.elements.val.length + tail.data.val.length) + 1 ≤ Usize.max := by
  have cost := initializer_cost_bytes encoding
  have segments := segment_count_bytes encoding
  have costEq := congrArg (fun raw : Module => raw.functions.length + 2 * raw.globals.length +
    (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length) matched.1
  have segmentEq := congrArg (fun raw : Module => raw.elements.length + raw.data.length) matched.1
  simp only [Itasca.Module.Elaboration.fromEnv, List.length_map, List.map_map,
    Function.comp_def, Itasca.Module.Environment.rawElement] at costEq segmentEq
  rw [costEq] at cost
  rw [segmentEq] at segments
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  norm_num [Itasca.limits.MAX_MODULE_BYTES, U32.max_eq] at bounded wordBound
  dsimp only [initializerMappingCost, initializerElementCost]
  constructor <;> omega

end Itasca.Compiler

end

/-! ## Initializer Source Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Binary

/-- The actual fresh compiler-driver input has enough space for initializer
lowering, directly from the independently encoded module and collected function
count. This covers successful lowering and every normal error result. -/
theorem initializer_lower_source_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (env : Itasca.metadata.Env) (tail : Itasca.metadata.Tail)
     (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (budget : runtime.compiler.Budget A) {R raw bytes}
    (encoding : ModuleEncodingWith R raw bytes)
    (matched : Itasca.Module.Elaboration.Matches env tail raw)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (functionCount : functions.val.length = env.func_type_indices.val.length) :
    runtime.compiler.initialize.lower ops (uninitializedModule env tail functions) budget
      ⦃ _ => True ⦄ := by
  obtain ⟨mapSpace, segmentSpace⟩ := initializer_source_headroom encoding matched bounded
  apply initializer_lower_fresh_total ops law _ budget rfl rfl rfl rfl
  · simpa only [uninitializedModule, functionCount] using mapSpace
  · exact segmentSpace

end Itasca.Compiler

end

end

/-! ## SubmitTotal -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Queue publication is safe once reached entry states provide bounded queue
headroom. The successful entry invariant is not required after a rejection. -/
theorem compiler_submit_total_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (safe : CompileScheduler A → stream.StreamingBatch → Prop)
    (entries : ∀ scheduler worker, safe scheduler worker →
      CompileScheduler.compile_entry ops scheduler worker ⦃ out =>
        out.1 = .Ok () → safe out.2.1 out.2.2 ⦄)
    (room : ∀ scheduler worker, safe scheduler worker → scheduler.completed.val.length < Usize.max)
    (scheduler : CompileScheduler A) (worker : stream.StreamingBatch)
    (held : safe scheduler worker) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops scheduler worker
      ⦃ _ => True ⦄ := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch.total ops law safe entries room scheduler worker held

end Itasca.Compiler

end

/-! ## SchedulerSubmissionSafety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

theorem CompileEntryWitness.scheduler_ready {A : Type} {ops : runtime.platform.Alloc A}
    {before after : CompileScheduler A} {worker finalWorker : stream.StreamingBatch}
    (entry : CompileEntryWitness ops before after worker finalWorker)
    {env : metadata.Env} {cursor : Nat} (ready : SchedulerReady env cursor before) :
    SchedulerReady env cursor after := by
  rw [entry.published]
  refine ⟨ready.signatures,ready.functionSlots,?_,ready.origin,ready.queue,ready.cursorBound⟩
  simpa only [alloc.vec.Vec.set_val_eq,List.length_set] using ready.functions

/-- The queue's headroom follows the issued cursor, rather than a separate
allocator assumption. Entry termination is required only for this batch's
actual dispatch/validation successors. -/
theorem compiler_submit_safety {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (env : metadata.Env)
    (issued : Stream.Batch.Issued) (sameEnv : issued.env = env) (bounded : issued.Bounded)
    (scheduler : CompileScheduler A) (ready : SchedulerReady env issued.first_func.val scheduler)
    (entries : ∀ current worker, SchedulerReady env issued.first_func.val current →
      Stream.Batch.Reachable issued worker → CompileScheduler.compile_entry ops current worker ⦃ _ => True ⦄) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops scheduler issued.seed ⦃ out =>
      out.1 = .Ok () → SchedulerReady env (issued.first_func.val + issued.num_funcs.val) out.2 ⦄ := by
  let safe := fun (current : CompileScheduler A) (worker : stream.StreamingBatch) => SchedulerReady env issued.first_func.val current ∧
    Stream.Batch.Reachable issued worker
  have entrySafe : ∀ current worker, safe current worker →
      CompileScheduler.compile_entry ops current worker ⦃ out => out.1 = .Ok () → safe out.2.1 out.2.2 ⦄ := by
    intro current worker held
    obtain ⟨⟨status,after,batch⟩,run,_⟩ := WP.spec_imp_exists (entries current worker held.1 held.2)
    rw [run]
    apply (WP.spec_ok _).mpr
    intro accepted
    dsimp only at accepted
    obtain ⟨w⟩ := compile_entry_accepted ops current after worker batch (by simpa only [accepted] using run)
    exact ⟨w.scheduler_ready held.1,w.reachable held.2⟩
  have room : ∀ current worker, safe current worker → current.completed.val.length < Usize.max := by
    intro current worker held
    have count := bounded.1
    have extent := bounded.2.1
    rw [sameEnv] at extent
    have queue := held.1.queue
    have max := env.func_type_indices.property
    omega
  obtain ⟨⟨status,after⟩,run,_⟩ := WP.spec_imp_exists
    (compiler_submit_total_on ops law safe entrySafe room scheduler issued.seed ⟨ready,.seed⟩)
  rw [run]
  apply (WP.spec_ok _).mpr
  intro accepted
  dsimp only at accepted
  obtain ⟨middle,worker,compiled,queue,updated⟩ := compiler_submit_accepted ops law scheduler after issued.seed
    (by simpa only [accepted] using run)
  have retained := compiled.fold (fun current _ => SchedulerReady env issued.first_func.val current)
    ready (fun _ _ _ _ held w => w.scheduler_ready held)
  have bound : issued.first_func.val + issued.num_funcs.val ≤ env.func_type_indices.val.length := by
    simpa only [sameEnv] using bounded.2.1
  refine ⟨?_,?_,?_,?_,?_,bound⟩
  · rw [updated]
    exact retained.signatures
  · rw [updated]
    exact retained.functionSlots
  · rw [updated]
    exact retained.functions
  · rw [updated]
    exact retained.origin
  · rw [queue,List.length_append,List.length_singleton]
    have := ready.queue
    have := bounded.1
    omega

end Itasca.Compiler

end

/-! ## CompileTotalDriver -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Common driver assembly from the reached streaming phase. This internal
adapter derives source initializer space and all result/error bookkeeping. -/
theorem compile_with_total_of_streaming {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits)
    (streaming : ∀ (codeStart codeEnd : Usize) (storage : metadata.Env),
      codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length →
      stream.validate_streaming CompileSource.Insts.ItascaStreamStreamingSource
        (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
        {bytes,code_start := codeStart,code_end := codeEnd}
        (initialScheduler A limits codeStart) storage ⦃ out =>
          out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ := by
  apply runtime.compiler.compile_with.total ops law bytes limits
  · intro codeStart codeEnd storage bounds
    exact WP.spec_mono (streaming codeStart codeEnd storage bounds) (fun _ _ => trivial)
  · intro codeStart codeEnd storage env scheduler tail functions budget pending bounds validated tailReady collect
    have ready := streaming codeStart codeEnd storage bounds
    rw [validated, WP.spec_ok] at ready
    have held := ready rfl
    obtain ⟨raw, encoding, matched, _, bounded⟩ := compiler_stream_source ops law bytes limits
      codeStart codeEnd storage env scheduler tail bounds tailReady validated
    have order := collect_functions_spec ops law scheduler.budget scheduler.functions
    rw [collect, WP.spec_ok] at order
    have count : functions.val.length = env.func_type_indices.val.length := by
      have eq := congrArg List.length (order functions rfl)
      simp only [List.length_map] at eq
      exact eq.symm.trans held.functions
    exact initializer_lower_source_total ops law env tail functions budget encoding matched bounded count

end Itasca.Compiler

end

/-! ## SchedulerSafety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

def ReachedEntriesTotal {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (env : metadata.Env) (issued : Stream.Batch.Issued) (scheduler : CompileScheduler A)
    (worker : stream.StreamingBatch), issued.env = env → issued.Bounded → CodeEntry.Bounds env →
    CodeEntry.EnvironmentWithinLimits env →
    SchedulerReady env issued.first_func.val scheduler →
    Stream.Batch.Reachable issued worker → CompileScheduler.compile_entry ops scheduler worker ⦃ _ => True ⦄

theorem compiler_scheduler_callbacks_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (entries : ReachedEntriesTotal ops) :
    Stream.Scheduler.CallbacksOn (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      SchedulerInitial (fun env cursor scheduler => SchedulerReady env cursor scheduler ∧ CodeEntry.EnvironmentWithinLimits env)
      (CodeEntry.EnvironmentWithinLimits) := by
  constructor
  · intro scheduler chunk
    exact ⟨(.Ok (),scheduler),rfl⟩
  · intro before chunk after accepted held
    have same : before = after := by simpa [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_metadataModuleVisitorInst.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.project_on_custom_section.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section.eq] using accepted
    simpa only [same] using held
  · intro env cursor before chunk after accepted held
    have same : before = after := by simpa [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_metadataModuleVisitorInst.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.project_on_custom_section.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section.eq] using accepted
    simpa only [same] using held
  · intro scheduler region held
    simpa [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_custom_region.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region.eq] using held
  · intro env cursor scheduler region held
    simpa [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_custom_region.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region.eq] using held
  · intro scheduler env held admitted bounds
    apply WP.spec_mono (compiler_environment_safety ops law scheduler env held)
    intro out fresh config accepted
    exact ⟨fresh config accepted,admitted⟩
  · intro env
    constructor
    · intro scheduler issued held sameEnv bounded bounds
      apply WP.spec_mono (compiler_submit_safety ops law env issued sameEnv bounded scheduler held.1
        (fun current worker ready reached => entries env issued current worker sameEnv bounded
          (by simpa only [sameEnv] using bounds) held.2 ready reached))
      intro out fresh accepted
      exact ⟨fresh accepted,held.2⟩
    · intro cursor scheduler held
      apply WP.spec_mono (compiler_poll_safety ops env cursor scheduler held.1)
      intro out fresh batch accepted
      exact ⟨fresh batch accepted,held.2⟩
  · intro env scheduler held
    simpa [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_code_end.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end.eq] using held
  · intro env scheduler tail held
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,WP.spec_ok]
    intro _
    exact ⟨⟨held.1.signatures,held.1.functionSlots,held.1.functions,held.1.origin,held.1.queue,held.1.cursorBound⟩,held.2⟩

/-- Actual environment decoding supplies the signature limits before any
worker is issued. It is retained through every reached scheduler state. -/
theorem compiler_stream_spec_of_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (entries : ReachedEntriesTotal ops) (source : CompileSource)
    (sourceBounds : SourceBounds source) (scheduler : CompileScheduler A)
    (initial : SchedulerInitial scheduler) (storage : metadata.Env) :
    stream.validate_streaming CompileSource.Insts.ItascaStreamStreamingSource
      (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage ⦃ out =>
        out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄ := by
  apply WP.spec_mono (stream.validate_streaming.spec_on CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage
    (source_callbacks_total source sourceBounds) SchedulerInitial
    (fun env cursor scheduler => SchedulerReady env cursor scheduler ∧ CodeEntry.EnvironmentWithinLimits env)
    (CodeEntry.EnvironmentWithinLimits) (compiler_scheduler_callbacks_on ops law entries) initial
    (by intro bytes env next bounded accepted
        exact (Module.Environment.accepted_entry_conditions bytes env next bounded accepted).2))
  intro out fresh accepted
  exact (fresh accepted).1
end Itasca.Compiler

end

/-! ## CompileTotal -/

section

/-!
Normal return of default and explicit-budget compilation, projecting the shared generic compiler totality proof.
-/

/-! ## Compile Default Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

@[step] theorem compiler_default_limits_total :
    CompileLimits.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
  unfold runtime.compiler.CompileLimits.Insts.CoreDefaultDefault.default
  step
  step

end Itasca.Compiler

end

/-! ## Compile CodeEntry Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Internal remaining body obligation, restricted to independently decoded
entry metadata, captured signature tables, and the actual fresh compiler/start
calls. It does not presume a successful body or final compilation. -/
def PreparedBodiesTotal {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (data : Slice U8) (env : metadata.Env) (index start : Usize)
    (signatures : Slice Signature) (functionSlots : Slice U32) (budget : Budget A)
    (batchStart : Usize) (initial started : FunctionCompiler A)
    (prepared : CodeEntry.Prepared data env index start),
    CodeEntry.Bounds env → CodeEntry.EnvironmentWithinLimits env → SignatureSequence signatures.val env.types.val →
    functionSlots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) →
    batchStart.val + data.length ≤ Usize.max →
    FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial →
    FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start ops initial prepared.ctx
      prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
    code.validate_body_with (FunctionCompiler.Insts.ItascaCodeOpVisitor ops) prepared.body env prepared.ctx
      prepared.typeIdx started ⦃ _ => True ⦄

/-- All entry dispatch, local decoding, start-callback and checker obligations
are discharged; the body proof is used only at the fresh state reached here. -/
theorem compiler_entries_total_of_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (bodies : PreparedBodiesTotal ops) : ReachedEntriesTotal ops := by
  intro env issued scheduler worker sameEnv bounded envBounds admitted held reached
  apply compiler_entry_total_of_validation ops scheduler issued worker bounded reached held.origin
  intro entry dispatched batchStart initial dispatch added created
  have reached' := Stream.Batch.Reachable.dispatch reached dispatch
  obtain ⟨_,_,workerEnv,workerCode,workerOffset,workerFirst,workerCount⟩ := reached'.validation.1
  have envEq : dispatched.env = env := workerEnv.trans sameEnv
  have maxRoom : limits.MAX_MODULE_BYTES.val + limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES]
    scalar_tac
  have addFits : scheduler.code_start.val + dispatched.code_offset.val ≤ Usize.max := by
    rw [workerOffset]
    have := bounded.2.2
    have := held.origin
    omega
  have arithmetic := Usize.add_spec (x := scheduler.code_start) (y := dispatched.code_offset) addFits
  rw [added,WP.spec_ok] at arithmetic
  have sourceFits : batchStart.val + dispatched.code.length ≤ Usize.max := by
    rw [workerCode]
    have bound := bounded.2.2
    have origin := held.origin
    rw [workerOffset] at arithmetic
    omega
  have range : dispatched.first_func.val + dispatched.num_funcs.val ≤ dispatched.env.func_type_indices.val.length := by
    simpa only [workerFirst,workerCount,workerEnv] using bounded.2.1
  apply Itasca.stream.StreamingBatch.validate_func.prepared_total _ dispatched entry.index initial
    (by simpa only [envEq] using envBounds) range
  · intro prepared
    exact prepared_compiler_start_total ops law prepared
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by have bound := prepared.body_bytes.bound; omega) created
  · intro prepared started startedCall
    have localBodies := bodies
    exact localBodies dispatched.code dispatched.env entry.index dispatched.validated_end
      (alloc.vec.Vec.deref scheduler.signatures) (alloc.vec.Vec.deref scheduler.func_param_slots)
      {scheduler.budget with marker := ()} batchStart initial started prepared
      (by simpa only [envEq] using envBounds)
      (by simpa only [envEq] using admitted)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.signatures)
      (by simpa [alloc.vec.Vec.deref,envEq] using held.functionSlots) sourceFits created startedCall

/-- Driver normality with the signature limits supplied by actual environment
validation. No restriction on the input bytes is required. -/
theorem compile_with_total_of_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits) (entries : ReachedEntriesTotal ops) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ := by
  apply compile_with_total_of_streaming ops law bytes limits
  intro codeStart codeEnd storage bounds
  by_cases small : codeStart.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  · exact compiler_stream_spec_of_entries ops law entries
      {bytes,code_start := codeStart,code_end := codeEnd} bounds _
      ⟨rfl,rfl,rfl,rfl,small⟩ storage
  · rw [compiler_stream_large_environment _
      {bytes,code_start := codeStart,code_end := codeEnd} bounds
      (by change Itasca.limits.MAX_MODULE_BYTES.val < codeStart.val; omega)]
    simp

/-- The complete driver reduces to body normality at valid, actually
prepared function entries. Header, local, initializer and checker paths are derived. -/
theorem compile_with_total_of_prepared_bodies {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits) (bodies : PreparedBodiesTotal ops) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ :=
  compile_with_total_of_entries ops law bytes limits
    (compiler_entries_total_of_prepared_bodies ops law bodies)
end Itasca.Compiler

end

end

/-! ## PreparedExecutableSafety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual entry setup supplies every static and allocation ledger field needed
by the reached-body normality proof, before reading any instruction. -/
theorem prepared_executable_safety {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start}
    (w : CodeEntry.Prepared data env index start)
    (small : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val + data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    let C := Translation.Environment.context env w.ctx
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    Translation.Environment.Matches env ⟨w.ctx.locals,w.ft.results⟩ C ∧
    IndexedTableReaderCompilerPoint (fun tables => ExecutableEmission tables C) started started
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Body.initial w.typeIdx) ∧
    ObservedStack started [] ∧
    started.function.indirect.val.length ≤ started.function.code.val.length ∧
    started.function.simd.val.length ≤ started.function.code.val.length ∧
    started.function.v128_pool.val.length ≤ started.function.code.val.length ∧
    FixupBudget started.frames.val started.function.code.val.length := by
  have endFits : batchStart.val + w.finish.val ≤ Usize.max := by
    have bound := w.body_bytes.bound
    omega
  obtain ⟨facts,point⟩ := indexed_table_prepared_compiler_initial
    (fun tables => ExecutableEmission tables (Translation.Environment.context env w.ctx))
    ops law w small signaturesMatch slotsMatch endFits created begun
  refine ⟨facts,?_,point,prepared_compiler_raw_initial ops law w signaturesMatch endFits created begun⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  simp only [Translation.Environment.context,w.context_results]

end Itasca.Compiler

end

/-! ## CompileTotal -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual prepared function bodies return normally for WebAssembly Core 2.0,
without a body-acceptance or callback-correctness premise. The initial source
and allocation invariants come from actual entry setup. -/
theorem prepared_bodies_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) :
    PreparedBodiesTotal ops := by
  intro data env index start signatures functionSlots budget batchStart initial started prepared
    bounds environment signaturesMatch slotsMatch batchBound created begun
  by_cases small : prepared.body.length ≤ limits.MAX_FUNCTION_BYTES.val
  · obtain ⟨facts,matched,point,observed,indirect,simd,pool,fixups⟩ :=
      prepared_executable_safety ops law prepared small signaturesMatch slotsMatch batchBound created begun
    have contextEq : prepared.ctx = ⟨prepared.ctx.locals,prepared.ft.results⟩ := by
      have results : prepared.ctx.results = prepared.ft.results :=
        alloc.vec.Vec.ext _ _ prepared.context_results
      cases h : prepared.ctx
      simp_all
    have body := compiler_body_total ops law started (Translation.Environment.context env prepared.ctx)
      (prepared.ctx.locals.val.map Translation.valueType) prepared.body env prepared.ctx.locals prepared.typeIdx prepared.ft
      point facts.localLayout facts.locals facts.functionSlots matched rfl facts.signatures
      ⟨observed,indirect,simd,pool,fixups⟩ facts.bodyBound
    rw [← contextEq] at body
    obtain ⟨result,run,_⟩ := WP.spec_imp_exists body
    simp [run]
  · rw [reader_body_too_large _ prepared.body env prepared.ctx prepared.typeIdx started (by omega)]
    simp

/-- Complete-module compilation returns success or a reported validation or
resource error on arbitrary bytes and arbitrary compiler limits. -/
@[step] theorem compile_with_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ :=
  compile_with_total_of_prepared_bodies ops law bytes limits
    (prepared_bodies_total ops law)

end Itasca.Compiler

end

end

/-! ## PreparationAndGlobalAvailability -/

section

/-!
Proofs for Runtime / Compiler / Module.

This module collects PreparationAndGlobalAvailability, InitializersAndDriverState, SchedulerCapacities.
Each section documents its contracts and consumers.
-/

/-! ## PreparationAndGlobalAvailability -/

section

open Itasca.Representation

/-!
# Preparation And Global Availability

Prepared functions and global initializers have the resources required by module compilation.
-/

/-! ## PreparedFunctionAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Source-derived conservative total charges for one prepared function. -/
abbrev preparedFunctionAllowance (ctx : code.Context) (length : Nat) : ChargeCounter → Nat
  | .instructions => 3*length
  | .branches => length
  | .controls => 1+length
  | .locals => ctx.locals.val.length

end Itasca.Compiler

end

/-! ## SourceEntryPrepared -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Forget visitor observations while retaining the independently decoded
source entry. No compiler result occurs in this record. -/
def preparedOfSourceWitness {V : Type} {visitor : code.OpVisitor V} {data env index start finish before after}
    (w : CodeEntry.Witness visitor data env index start finish before after) :
    CodeEntry.Prepared data env index start where
  finish := finish
  typeIdx := w.typeIdx
  ft := w.ft
  groups := w.groups
  ctx := w.ctx
  content := w.content
  bodyStart := w.bodyStart
  body := w.body
  size := w.size
  index_lt := w.index_lt
  index_type := w.index_type
  type_lt := w.type_lt
  function_type := w.function_type
  header := w.header
  extent := w.extent
  locals_bytes := w.locals_bytes
  locals_bound := w.locals_bound
  context_locals := w.context_locals
  context_results := w.context_results
  body_bytes := w.body_bytes

/-- Independent entry encoding and typing construct prepared source metadata
and body validity, with no compiler visitor or accepted target trace. -/
theorem source_entry_prepared (data : Slice U8) (env : metadata.Env) (index start finish : Usize)
     (entry : Binary.Code)
    (indexBound : index.val < env.func_type_indices.val.length)
    (typed : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (bounds : CodeEntry.Bounds env)
    (limits : CodeEntry.EnvironmentWithinLimits env)
    (encoded : Binary.At (CodeEntry.CodeEncodingWithinLimits) data start entry finish) :
    ∃ w : CodeEntry.Prepared data env index start,
      w.finish = finish ∧ Body.Validated w.body env w.ctx.locals w.typeIdx ∧
      w.body.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val := by
  obtain ⟨⟨reply,after⟩,called,accepted⟩ := WP.spec_imp_exists
    (metadata.validate_code_entry_with.complete_spec_of_body code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor
      Visitor.empty_accepts data start env index entry finish () indexBound typed bounds encoded (by
        intro body ctx typeIdx ft signature results size bodyValid started
        exact code.validate_body_with.complete _ Visitor.empty_accepts body env ctx typeIdx
          limits size bodyValid started))
  dsimp only at accepted
  subst reply
  obtain ⟨w⟩ := metadata.validate_code_entry_with.witness code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor
    data start env index finish () after bounds called
  refine ⟨preparedOfSourceWitness w,rfl,?_,?_⟩
  · exact code.validate_body_with.sound _ w.body env w.ctx w.typeIdx w.startedState after
      w.body_accepted
  · exact (witness_typed_steps w).body_size

end Itasca.Compiler

end

/-! ## EntryAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Independent numerical resource eligibility over decoded source entry
metadata. This mentions no target callback, emitted function, or target run. -/
def EntryResourceDemand {A : Type} (budget : runtime.compiler.Budget A)
    (data : Slice U8) (env : metadata.Env) (index start : Usize)
     (bound : Nat) : Prop :=
  ∀ w : CodeEntry.Prepared data env index start,
    PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound

end Itasca.Compiler

end

/-! ## SourceQueuePolicy -/

section

namespace Itasca.Compiler.StreamAvailability
open Aeneas Aeneas.Std Itasca

/-- Local acceptance contract at a fixed validated environment and source
cursor. Unlike an unrestricted visitor contract, this permits finite numerical
module budgets and retains actual completed worker identities and finish checks. -/
structure QueuePolicy {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.StreamingConfig) (env : metadata.Env)
    (codeBytes : Nat) (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop) : Prop where
  batch_positive : 0 < config.batch_bytes.val
  capacity_positive : 0 < config.max_batches.val
  submit : ∀ id queue cursor issued before,
    Queued id queue cursor before → Stream.Scheduler.Valid issued →
    issued.env = env → issued.module_id = id → issued.first_func.val = cursor →
    queue.length < config.max_batches.val → issued.code.length ≤ codeBytes →
    ∃ after, visitor.submit_code_batch before issued.seed = .ok (.Ok (),after) ∧
      Queued id (queue++[issued]) (cursor+issued.num_funcs.val) after
  poll : ∀ id queue cursor before, Queued id queue cursor before → queue ≠ [] →
    ∃ issued rest worker after, (issued::rest).Perm queue ∧
      visitor.poll_code_batch before = .ok (.Ok worker,after) ∧
      Stream.Batch.Identity issued worker ∧ Itasca.stream.StreamingBatch.finish worker = .ok (.Ok ()) ∧
      Queued id rest cursor after

/-- A real queued worker retires successfully. Its finish proof comes from
concrete compilation; dispatch cursors need not match an empty visitor run. -/
theorem retire_complete {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.StreamingConfig) (env : metadata.Env)
    (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    {codeBytes : Nat} (policy : QueuePolicy visitor config env codeBytes Queued)
    (id : U64) (queue : List Stream.Batch.Issued) (cursor : Nat) (before : V)
    (pending : alloc.vec.Vec Usize) (held : Queued id queue cursor before)
    (valid : Stream.Scheduler.ValidQueue id queue)
    (ids : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id)) (nonempty : pending.val ≠ []) :
    ∃ after remaining rest,
      Itasca.stream.retire_code_batch visitor id before pending = .ok (.Ok (),after,remaining) ∧
      Queued id rest cursor after ∧ Stream.Scheduler.ValidQueue id rest ∧
      remaining.val.Perm (rest.map Stream.Batch.Issued.batch_id) ∧ remaining.length+1 = pending.length := by
  have queued : queue ≠ [] := by
    intro empty
    have length := ids.length_eq
    simp only [empty,List.map_nil,List.length_nil] at length
    exact nonempty (by simpa using length)
  obtain ⟨issued,rest,worker,after,permutation,polled,identity,finished,retained⟩ := policy.poll id queue cursor before held queued
  have member : issued ∈ queue := permutation.mem_iff.mp (by simp)
  obtain ⟨moduleId,_⟩ := valid issued member
  have pendingIds : (issued.batch_id::rest.map Stream.Batch.Issued.batch_id).Perm pending.val :=
    (permutation.map Stream.Batch.Issued.batch_id).trans ids.symm
  obtain ⟨remaining,retired,removed⟩ := Itasca.stream.retire_code_batch.complete visitor id before after pending worker polled
    (identity.1.trans moduleId) (by rw [identity.2.1]; exact pendingIds.mem_iff.mp (by simp)) finished
  refine ⟨after,remaining,rest,retired,retained,?_,?_,?_⟩
  · intro old member
    exact valid old (permutation.mem_iff.mp (by simp [member]))
  · rw [identity.2.1] at removed
    exact List.Perm.cons_inv (removed.trans pendingIds.symm)
  · have length := removed.length_eq
    simpa only [List.length_cons] using length

/-- Draining the actual completed-worker queue preserves the source cursor and
terminates with every pending worker retired. -/
theorem drain_complete {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.StreamingConfig) (env : metadata.Env)
    (Queued : U64 → List Stream.Batch.Issued → Nat → V → Prop)
    {codeBytes : Nat} (policy : QueuePolicy visitor config env codeBytes Queued)
    (id : U64) (queue : List Stream.Batch.Issued) (cursor : Nat) (before : V)
    (pending : alloc.vec.Vec Usize) (held : Queued id queue cursor before)
    (valid : Stream.Scheduler.ValidQueue id queue)
    (ids : pending.val.Perm (queue.map Stream.Batch.Issued.batch_id)) :
    ∃ after remaining,
      Itasca.stream.retire_all_code_batches visitor id before pending = .ok (.Ok (),after,remaining) ∧
      remaining.val = [] ∧ Queued id [] cursor after := by
  generalize count : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing queue before pending with
  | h n ih =>
    by_cases empty : pending.val = []
    · have queueEmpty : queue = [] := by
        have length := ids.length_eq
        simp only [empty,List.length_nil,List.length_map] at length
        simpa using length.symm
      refine ⟨before,pending,?_,empty,by simpa only [queueEmpty] using held⟩
      rw [Itasca.stream.retire_all_code_batches,Itasca.stream.retire_all_code_batches_loop,loop]
      simp [Itasca.stream.retire_all_code_batches_loop.body,alloc.vec.Vec.is_empty,empty]
    · obtain ⟨middle,remaining,rest,retired,retained,restValid,restIds,length⟩ :=
        retire_complete visitor config env Queued policy id queue cursor before pending held valid ids empty
      change remaining.val.length+1 = pending.val.length at length
      obtain ⟨after,final,continued,finished,result⟩ := ih remaining.val.length (by omega)
        rest middle remaining retained restValid restIds rfl
      refine ⟨after,final,?_,finished,result⟩
      rw [Itasca.stream.retire_all_code_batches,Itasca.stream.retire_all_code_batches_loop,loop]
      have nonempty : pending.val.isEmpty = false := by simpa using empty
      simpa [Itasca.stream.retire_all_code_batches_loop.body,alloc.vec.Vec.is_empty,nonempty,retired,
        core.result.Result.Insts.CoreOpsTry.branch,Itasca.stream.retire_all_code_batches,
        Itasca.stream.retire_all_code_batches_loop] using continued

end Itasca.Compiler.StreamAvailability

end

/-! ## EnvironmentReadyAvailable -/

section

/-!
Successful compiler environment capture, from signature and function slots through the completed function vector. EnvironmentDemand bounds the requests needed to reach the ready compiler environment.
-/

/-! ## Environment Ready Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual environment-ready callback accepts from independent source
widths, input limits, and allocation demand. No accepted callback trace is
supplied. All budget counters remain unchanged in this metadata phase. -/
theorem environment_ready_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.metadata.Env)
    (demand : EnvironmentDemand scheduler env bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env
      ⦃ out => out.1 = .Ok ⟨25000#usize,4#usize⟩ ∧ out.2.budget = scheduler.budget ⦄ := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.available ops bound available scheduler env demand

end Itasca.Compiler

end

end

/-! ## InitializerGlobalsAvailable -/

section

/-!
Availability of constant/global initializers and their global-segment fold.
-/

/-! ## Initializer Availability -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- A checked global initializer publishes both its synthetic function and its
mapping under an independent combined-vector demand bound. -/
theorem initializer_global_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val < module.module.env.globals.val.length)
    (typed : ∀ global ∈ module.module.env.globals.val,
      Itasca.Module.Constants.Valid module.module.env global.init global.gtype.valtype)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 2 ≤ bound)
    (capacity : initializerSize module + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_global ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 = initializerSize module + 2 ⦄ := by
  let global := module.module.env.globals.val[index.val]'inside
  have found : module.module.env.globals.val[index.val]? = some global := List.getElem?_eq_getElem inside
  have valid := typed global (List.getElem_mem inside)
  have vector : ∀ lo hi, global.init = .V128 lo hi → global.gtype.valtype = .V128 := by
    intros lo hi matching
    rw [matching] at valid
    generalize valueTypeEq : global.gtype.valtype = valueType at valid ⊢
    cases valid
    rfl
  apply WP.spec_mono (runtime.compiler.initialize.lower_global.available ops bound available module budget index global found
    vector instructions codeRequest
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega))
  rintro ⟨status, after, afterBudget⟩ ⟨accepted, count, limits, frame, mapped, function, certified, appended⟩
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨accepted, count, limits, moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  rw [mapped, appended]
  simp only [List.length_append, List.length_singleton]
  omega

end Itasca.Compiler

end

/-! ## Initializer Globals Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every remaining independently typed global is accepted by the actual
initializer loop. The demand is computed from the source global count, not
from an assumed accepted compilation or emitted-code certificate. -/
theorem initializer_globals_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.env.globals.val.length)
    (typed : ∀ global ∈ module.module.env.globals.val,
      Itasca.Module.Constants.Valid module.module.env global.init global.gtype.valtype)
    (instructions : budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + 2*(module.module.env.globals.val.length-index.val) ≤ bound)
    (capacity : initializerSize module + 2*(module.module.env.globals.val.length-index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop0 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧
      initializerSize out.1 = initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      out.2.1.instructions.val = budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ∧
      out.2.1.limits = budget.limits ⦄ := by
  let P := fun current (charged : runtime.compiler.Budget A) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + 2 * (module.module.env.globals.val.length - cursor.val) =
      initializerSize module + 2 * (module.module.env.globals.val.length - index.val) ∧
    charged.instructions.val + 2 * (module.module.env.globals.val.length - cursor.val) =
      budget.instructions.val + 2 * (module.module.env.globals.val.length - index.val)
  change WP.spec (loop (initializerGlobalLoop ops).body (module, budget, index, .Ok ())) _
  apply InitializerModuleLoop.available
    { rules := initializerGlobalLoop ops, before := module, budget := budget, j := index,
      length := alloc.vec.Vec.len module.module.env.globals, lengthEq := rfl, bounded := inside, P := P,
      Q := (fun after afterBudget => after.module = module.module ∧
      initializerSize after = initializerSize module + 2*(module.module.env.globals.val.length-index.val) ∧
      afterBudget.instructions.val = budget.instructions.val + 2*(module.module.env.globals.val.length-index.val) ∧
      afterBudget.limits = budget.limits), advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source position prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val < module.module.env.globals.val.length at position
    have currentBound : cursor.val < current.module.env.globals.val.length := by
      simpa only [source] using position
    apply WP.spec_mono (initializer_global_available ops bound available current charged cursor currentBound
      (by simpa only [source] using typed) (by rw [limits]; omega) codeRequest (by omega) (by omega))
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega⟩
  · intro current charged cursor source last prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val = module.module.env.globals.val.length at last
    exact ⟨source, by omega, by omega, limits⟩
  · exact ⟨rfl, by omega, by omega⟩

end Itasca.Compiler

end

end

end

/-! ## InitializersAndDriverState -/

section

open Itasca.Representation

/-!
# Initializers And Driver State

Initializer availability and driver frames preserve the module compiler state across preparation.
-/

/-! ## InitializerDataAvailable -/

section

/-!
Successful data initializer compilation from independently bounded source offsets and allocator availability.
-/

/-! ## Initializer Data Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Active offsets compile from independent constant-expression typing;
passive data needs only its mapping append. Both paths accept from conservative
source-independent reserve and two-instruction headroom bounds. -/
theorem initializer_data_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val < module.module.tail.data.val.length)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 2 ≤ bound)
    (capacity : initializerSize module + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + 2 ⦄ := by
  let segment := module.module.tail.data.val[index.val]'inside
  have found : module.module.tail.data.val[index.val]? = some segment := List.getElem?_eq_getElem inside
  have scalar : ∀ memory offset, segment.mode = .Active memory offset → ∀ lo hi, offset ≠ .V128 lo hi := by
    intros memory offset mode lo hi matching
    have valid := typed segment (List.getElem_mem inside) memory offset mode
    rw [matching] at valid
    cases valid
  apply WP.spec_mono (runtime.compiler.initialize.lower_data_offset.available ops bound available module budget index segment found
    scalar instructions codeRequest
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega))
  rintro ⟨status, after, afterBudget⟩ ⟨accepted, count, limits, frame, functions, offsets⟩
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨accepted, count, limits, moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  omega

end Itasca.Compiler

end

/-! ## Initializer Data Offsets Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Every remaining independently typed data offset is accepted by the actual
initializer loop. The demand is computed from the source data count, not
from an assumed accepted compilation or emitted-code certificate. -/
theorem initializer_data_offsets_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + 2*(module.module.tail.data.val.length-index.val) ≤ bound)
    (capacity : initializerSize module + 2*(module.module.tail.data.val.length-index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop2 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧
      initializerSize out.1 ≤ initializerSize module + 2*(module.module.tail.data.val.length-index.val) ∧
      out.2.1.instructions.val ≤ budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ∧
      out.2.1.limits = budget.limits ⦄ := by
  let P := fun current (charged : runtime.compiler.Budget A) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + 2 * (module.module.tail.data.val.length - cursor.val) ≤
      initializerSize module + 2 * (module.module.tail.data.val.length - index.val) ∧
    charged.instructions.val + 2 * (module.module.tail.data.val.length - cursor.val) ≤
      budget.instructions.val + 2 * (module.module.tail.data.val.length - index.val)
  change WP.spec (loop (initializerDataOffsetLoop ops).body (module, budget, index, .Ok ())) _
  apply InitializerModuleLoop.available
    { rules := initializerDataOffsetLoop ops, before := module, budget := budget, j := index,
      length := alloc.vec.Vec.len module.module.tail.data, lengthEq := rfl, bounded := inside, P := P,
      Q := (fun after afterBudget => after.module = module.module ∧
      initializerSize after ≤ initializerSize module + 2*(module.module.tail.data.val.length-index.val) ∧
      afterBudget.instructions.val ≤ budget.instructions.val + 2*(module.module.tail.data.val.length-index.val) ∧
      afterBudget.limits = budget.limits), advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source position prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val < module.module.tail.data.val.length at position
    have currentBound : cursor.val < current.module.tail.data.val.length := by
      simpa only [source] using position
    apply WP.spec_mono (initializer_data_offset_available ops bound available current charged cursor currentBound
      (by simpa only [source] using typed) (by rw [limits]; omega) codeRequest (by omega) (by omega))
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega⟩
  · intro current charged cursor source last prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val = module.module.tail.data.val.length at last
    exact ⟨source, by omega, by omega, limits⟩
  · exact ⟨rfl, by omega, by omega⟩

end Itasca.Compiler

end

end

/-! ## InitializerElementsAvailable -/

section

/-!
Availability of individual element initializers and their complete element-segment fold.
-/

/-! ## Initializer Elements Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The complete element-mapping loop accepts from source typing and a demand
computed by summing source initializer counts plus three entries per segment.
Temporary element-index vectors are bounded by this same independent demand. -/
theorem initializer_elements_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize)
    (inside : index.val ≤ module.module.env.elements.val.length)
    (typed : ∀ segment ∈ module.module.env.elements.val, ∀ expr ∈ segment.init.val,
      Itasca.Module.Constants.Valid module.module.env expr (Itasca.Module.Constants.referenceValueType segment.elem))
    (offsetTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ≤ bound)
    (capacity : initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop1 ops module budget index (.Ok ()) ⦃ out =>
      out.2.2 = .Ok () ∧ out.1.module = module.module ∧ out.2.1.limits = budget.limits ∧
      initializerSize out.1 ≤ initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
      out.2.1.instructions.val ≤ budget.instructions.val +
        2*initializerElementCost (module.module.env.elements.val.drop index.val) ⦄ := by
  let P := fun current (charged : runtime.compiler.Budget A) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + initializerElementCost (module.module.env.elements.val.drop cursor.val) ≤
      initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
    charged.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop cursor.val) ≤
      budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val)
  change WP.spec (loop (initializerElementLoop ops).body (module, budget, index, .Ok ())) _
  apply InitializerModuleLoop.available
    { rules := initializerElementLoop ops, before := module, budget := budget, j := index,
      length := alloc.vec.Vec.len module.module.env.elements, lengthEq := rfl, bounded := inside, P := P,
      Q := fun after afterBudget => after.module = module.module ∧ afterBudget.limits = budget.limits ∧
        initializerSize after ≤ initializerSize module + initializerElementCost (module.module.env.elements.val.drop index.val) ∧
        afterBudget.instructions.val ≤ budget.instructions.val + 2*initializerElementCost (module.module.env.elements.val.drop index.val),
      advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source position prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val < module.module.env.elements.val.length at position
    let segment := module.module.env.elements.val[cursor.val]'position
    have found : module.module.env.elements.val[cursor.val]? = some segment := List.getElem?_eq_getElem position
    have member := List.getElem_mem position
    have cost := initializer_element_cost_step _ _ _ found
    have initLength : segment.init.length = segment.init.val.length := rfl
    apply WP.spec_mono (runtime.compiler.initialize.lower_element.available ops bound available current charged cursor segment
      ⟨by simpa only [source] using found, by simpa only [source] using typed segment member,
        by simpa only [source] using offsetTyped segment member,
        by rw [limits]; omega, codeRequest, by omega, by omega⟩)
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    dsimp only [P]
    rw [increment]
    exact ⟨limitsAgain.trans limits, by omega, by omega⟩
  · intro current charged cursor source last prior
    obtain ⟨limits, size, used⟩ := prior
    change cursor.val = module.module.env.elements.val.length at last
    simp only [last, List.drop_length, initializerElementCost, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at size used
    exact ⟨source, limits, size, used⟩
  · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

end Itasca.Compiler

end

end

/-! ## CompileDriverFrame -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Compiler custom-section callbacks preserve every scheduler predicate. -/
theorem compiler_custom_preserves {A : Type} (ops : runtime.platform.Alloc A)
    (P : runtime.compiler.CompileScheduler A → Prop) :
    Module.Tail.PreservesInvariant
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst P := by
  intro before chunk after accepted prior
  have same : before = after := congrArg Prod.snd (Result.ok_injective accepted)
  simpa only [← same] using prior

/-- Parsing the environment only delivers custom-section notifications, so the
actual compiler scheduler is unchanged before its environment-ready callback. -/
theorem compiler_driver_decoded {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.StreamingSource S} {id state before after env}
    (run : Stream.Run.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env) : run.decoded = before := by
  have region : run.region = before := (Result.ok_injective run.region_call).symm
  have decoded := metadata.validate_env_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst
    (fun scheduler => scheduler = before) (compiler_custom_preserves ops _) run.environment run.region env
    run.environmentLength run.decoded run.decode_environment region
  exact decoded

/-- Code-end, tail parsing/delivery and final worker retirement preserve the
function array and captured tables produced by submission. -/
theorem compiler_driver_after_submission {A S : Type} (ops : runtime.platform.Alloc A)
    {source : stream.StreamingSource S} {id state env environmentLength before after}
    (run : Stream.Run.Remaining source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state env environmentLength before after) :
    after = {run.submitted with completed := after.completed, tail := some run.tail} := by
  have ended : run.ended = run.submitted := by
    have same := congrArg Prod.snd (Result.ok_injective run.end_call)
    exact same.symm
  have region : run.region = run.ended := (Result.ok_injective run.region_call).symm
  have decoded := metadata.validate_tail_with.accepted_invariant
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops).metadataModuleVisitorInst
    (fun scheduler => scheduler = run.region) (compiler_custom_preserves ops _) run.tailBytes 0#usize env
    run.region run.tail run.decodedTail run.decode_tail rfl
  have ready : run.ready = {run.decodedTail with tail := some run.tail} := by
    have same := congrArg Prod.snd (Result.ok_injective run.ready_call)
    exact same.symm
  have drained := compiler_drain_frame ops id run.ready after run.pending run.remaining run.drain_call
  simpa only [ready, decoded, region, ended] using drained

/-- Actual environment preparation supplies the exact canonical signature and
parameter tables and the empty source-indexed result array. -/
theorem compiler_driver_configured {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {source : stream.StreamingSource S} {id state before after env}
    (run : Stream.Run.Accepted source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      id state before after env)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) :
    SignatureSequence run.remaining.configured.signatures.val env.types.val ∧
      run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      run.remaining.configured.functions.val = List.replicate env.func_type_indices.val.length none ∧
      run.remaining.configured.code_start = before.code_start := by
  have decoded := compiler_driver_decoded ops run
  have prepared := compiler_environment_ready_sequence ops law run.decoded env
    (by simpa only [decoded] using emptyTypes) (by simpa only [decoded] using emptySlots)
    (by simpa only [decoded] using emptyFunctions)
  have configured := run.remaining.configured_call
  change runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops run.decoded env =
    .ok (.Ok run.remaining.config, run.remaining.configured) at configured
  rw [configured, WP.spec_ok] at prepared
  obtain ⟨signatures, widths, functions⟩ := prepared _ rfl
  have frame := compiler_environment_frame ops run.decoded run.remaining.configured env run.remaining.config
    run.remaining.configured_call
  have origin := congrArg (fun fields => fields.2.2) frame
  exact ⟨signatures, widths, functions, by simpa only [schedulerFrame, decoded] using origin⟩
end Itasca.Compiler

end

end

/-! ## SchedulerCapacities -/

section

/-! ## CompileSchedulerAssembly -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem source_functions_length {raw : Binary.Module}
    (count : raw.functions.length = raw.codes.length) :
    (sourceFunctions raw).length = raw.functions.length := by
  simp [sourceFunctions, List.length_zipWith, count]

end Itasca.Compiler

end

/-! ## CompileSourceSetup -/

section

/-! Shared scheduler configuration and code-coordinate transport for source
certificates. Function, slice and capacity proofs retain their distinct folds. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Configuration facts used by each source-ordered compiler body fold. -/
theorem CompileSourceCertificate.scheduler_setup {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    SignatureSequence c.run.remaining.configured.signatures.val w.env.types.val ∧
      c.run.remaining.configured.func_param_slots.val.map (fun word => word.val) =
        w.env.func_types.val.map (fun ft => signatureSlots ft.params.val) ∧
      c.run.remaining.configured.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  refine ⟨prepared.1,prepared.2.1,?_⟩
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  rw [prepared.2.2.2]
  change w.codeStart.val ≤ _
  exact bounds.1.trans (bounds.2.trans c.moduleBound)

/-- Transport the actual reader's code length to the coherent source slice. -/
theorem CompileSourceCertificate.code_length {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) : c.run.remaining.codeLength = Slice.len c.code := by
  apply UScalar.eq_of_val_eq
  exact c.coherent.code_len_eq _ c.run.remaining.length_call
end Itasca.Compiler

end

/-! ## CompileSlice -/

section

/-! Source-ordered slice certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual concrete source supplies every exact read used by the retained
canonical code-section certificate. -/
theorem CompileSourceCertificate.available {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) :
    Stream.Source.Available runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
      {bytes, code_start := w.codeStart, code_end := w.codeEnd} c.environment.val c.code.val c.tail.val := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have actual := source_available source bounds
  obtain ⟨len, readLen, length⟩ := actual.code_len_read
  have codeLength := c.coherent.code_len_eq len readLen
  constructor
  · obtain ⟨buffer, read, _⟩ := actual.environment_read
    exact ⟨buffer, read, c.coherent.environment_eq buffer read⟩
  · exact ⟨len, readLen, codeLength⟩
  · intro first last order bound
    obtain ⟨buffer, read, _⟩ := actual.code_read first last order (by omega)
    exact ⟨buffer, read, c.coherent.code_eq first last buffer order bound read⟩
  · obtain ⟨buffer, read, _⟩ := actual.tail_read
    exact ⟨buffer, read, c.coherent.tail_eq buffer read⟩

end Itasca.Compiler

end

/-! ## SchedulerCapacities -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Capacity certificates retained in the scheduler's sparse vector. -/
structure PendingModuleCapacities (env : metadata.Env)
    (pending : List (Option runtime.bytecode.CompiledFunction)) (sources : List funccode) : Prop where
  count : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32), env.func_type_indices.val[index]? = some typeIndex →
    ∃ compiled source, pending[index]? = some (some compiled) ∧ sources[index]? = some source ∧
      Representation.CompiledFunctionCapacity env typeIndex source compiled

theorem PendingModuleCapacities.collected {env pending sources}
    (certificate : PendingModuleCapacities env pending sources)
    (module : runtime.compiler.ExecutableModule) (sameEnv : module.module.env = env)

    (collected : pending = module.functions.val.map some) : ModuleCapacities module sources := by
  refine ⟨by simpa only [sameEnv] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, source, codeFound, sourceFound, code⟩ := certificate.entry index typeIndex
    (by simpa only [sameEnv] using found)
  refine ⟨compiled, source, ?_, sourceFound, by simpa only [sameEnv] using code⟩
  rw [collected, List.getElem?_map] at codeFound
  cases actual : module.functions.val[index]? <;> simp_all

/-- Every occupied scheduler slot carries the corresponding declared function
certificate. Empty slots are permitted until actual collection succeeds. -/
structure PartialModuleCapacities (env : metadata.Env) (sources : List funccode)
    (pending : List (Option runtime.bytecode.CompiledFunction)) : Prop where
  count : pending.length = env.func_type_indices.val.length
  sourceCount : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (compiled : runtime.bytecode.CompiledFunction),
    pending[index]? = some (some compiled) →
    ∃ typeIndex source, env.func_type_indices.val[index]? = some typeIndex ∧
      sources[index]? = some source ∧ Representation.CompiledFunctionCapacity env typeIndex source compiled

theorem PartialModuleCapacities.empty (env : metadata.Env) (sources : List funccode)
    (count : sources.length = env.func_type_indices.val.length) :
    PartialModuleCapacities env sources (List.replicate env.func_type_indices.val.length none) := by
  refine ⟨by simp, count, ?_⟩
  intro index compiled found
  have member := List.mem_of_getElem? found
  simp at member

theorem PartialModuleCapacities.set {env sources pending}
    (certificate : PartialModuleCapacities env sources pending)
    (index : Nat) (typeIndex : U32) (compiled : runtime.bytecode.CompiledFunction) (source : funccode)
    (lookup : env.func_type_indices.val[index]? = some typeIndex)
    (sourceLookup : sources[index]? = some source)
    (code : Representation.CompiledFunctionCapacity env typeIndex source compiled) :
    PartialModuleCapacities env sources (pending.set index (some compiled)) := by
  refine ⟨by simpa using certificate.count, certificate.sourceCount, ?_⟩
  intro other value found
  by_cases equal : other = index
  · subst other
    have bound : index < pending.length := by
      rw [certificate.count]
      exact (List.getElem?_eq_some_iff.mp lookup).1
    have same : compiled = value := by simpa [List.getElem?_set, bound] using found
    subst value
    exact ⟨typeIndex, source, lookup, sourceLookup, code⟩
  · apply certificate.entry other value
    simpa [List.getElem?_set, equal] using found

/-- The accepted entry's actual source-indexed write preserves all earlier
certificates and installs precisely its newly checked function. -/
theorem CompileEntryWitness.capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
     {env : metadata.Env} {sources : List funccode}
    (certificate : PartialModuleCapacities env sources before.functions.val)
    (typeIndex : U32) (source : funccode)
    (lookup : env.func_type_indices.val[w.entry.index.val]? = some typeIndex)
    (sourceLookup : sources[w.entry.index.val]? = some source)
    (code : Representation.CompiledFunctionCapacity env typeIndex source w.final.function) :
    PartialModuleCapacities env sources after.functions.val := by
  rw [w.published]
  simpa only [alloc.vec.Vec.set_val_eq] using certificate.set w.entry.index.val typeIndex w.final.function source lookup sourceLookup code

/-- Successful dense collection fills every slot, allowing the retained
per-index source witnesses to be assembled into the complete module list. -/
theorem PartialModuleCapacities.complete {env sources pending}
    (certificate : PartialModuleCapacities env sources pending)
    (functions : List runtime.bytecode.CompiledFunction)
    (collected : pending = functions.map some) :
    PendingModuleCapacities env pending sources := by
  have length : functions.length = env.func_type_indices.val.length := by
    simpa only [collected, List.length_map] using certificate.count
  refine ⟨certificate.sourceCount, ?_⟩
  intro index typeIndex lookup
  have bound : index < functions.length := by
    rw [length]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have found : pending[index]? = some (some functions[index]) := by simp [collected, bound]
  obtain ⟨actualType, source, actualLookup, sourceLookup, code⟩ := certificate.entry index functions[index] found
  have same : actualType = typeIndex := by simpa [lookup] using actualLookup.symm
  subst actualType
  exact ⟨functions[index], source, found, sourceLookup, code⟩
end Itasca.Compiler

end

end

end

/-! ## CompileExecutable -/

section

open Itasca.Representation

/-!
# Compile Executable

Entry certificates and scheduler submission assemble executable function collections. The final module compilation construction preserves source order and emitted-code witnesses.
-/

/-! ## ExecutableCollectedFunctions -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
structure PendingExecutableModuleFunctions (env : Itasca.metadata.Env)
    (pending : List (Option runtime.bytecode.CompiledFunction)) (sources : List funccode) : Prop where
  count : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32), env.func_type_indices.val[index]? = some typeIndex →
    ∃ compiled source, pending[index]? = some (some compiled) ∧ sources[index]? = some source ∧
      DefinedExecutableFunctionCode env typeIndex source compiled

/-- Source-indexed compiler certificates survive actual dense collection. -/
theorem PendingExecutableModuleFunctions.collected {env pending sources}
    (certificate : PendingExecutableModuleFunctions env pending sources)
    (module : runtime.compiler.ExecutableModule) (sameEnv : module.module.env = env)
    (collected : pending = module.functions.val.map some) : ExecutableModuleFunctions module sources := by
  refine ⟨by simpa only [sameEnv] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, source, codeFound, sourceFound, code⟩ := certificate.entry index typeIndex
    (by simpa only [sameEnv] using found)
  refine ⟨compiled, source, ?_, sourceFound, by simpa only [sameEnv] using code⟩
  rw [collected, List.getElem?_map] at codeFound
  cases actual : module.functions.val[index]? <;> simp_all
end Itasca.Compiler

end

/-! ## ExecutableSchedulerFunctions -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every occupied scheduler slot carries the corresponding declared function
certificate. Empty slots are permitted until actual collection succeeds. -/
structure PartialExecutableModuleFunctions (env : metadata.Env) (sources : List funccode)
    (pending : List (Option runtime.bytecode.CompiledFunction)) : Prop where
  count : pending.length = env.func_type_indices.val.length
  sourceCount : sources.length = env.func_type_indices.val.length
  entry : ∀ (index : Nat) (compiled : runtime.bytecode.CompiledFunction),
    pending[index]? = some (some compiled) →
    ∃ typeIndex source, env.func_type_indices.val[index]? = some typeIndex ∧
      sources[index]? = some source ∧ DefinedExecutableFunctionCode env typeIndex source compiled

theorem PartialExecutableModuleFunctions.empty (env : metadata.Env) (sources : List funccode)
    (count : sources.length = env.func_type_indices.val.length) :
    PartialExecutableModuleFunctions env sources (List.replicate env.func_type_indices.val.length none) := by
  refine ⟨by simp, count, ?_⟩
  intro index compiled found
  have member := List.mem_of_getElem? found
  simp at member

theorem PartialExecutableModuleFunctions.set {env sources pending}
    (certificate : PartialExecutableModuleFunctions env sources pending)
    (index : Nat) (typeIndex : U32) (compiled : runtime.bytecode.CompiledFunction) (source : funccode)
    (lookup : env.func_type_indices.val[index]? = some typeIndex)
    (sourceLookup : sources[index]? = some source)
    (code : DefinedExecutableFunctionCode env typeIndex source compiled) :
    PartialExecutableModuleFunctions env sources (pending.set index (some compiled)) := by
  refine ⟨by simpa using certificate.count, certificate.sourceCount, ?_⟩
  intro other value found
  by_cases equal : other = index
  · subst other
    have bound : index < pending.length := by
      rw [certificate.count]
      exact (List.getElem?_eq_some_iff.mp lookup).1
    have same : compiled = value := by simpa [List.getElem?_set, bound] using found
    subst value
    exact ⟨typeIndex, source, lookup, sourceLookup, code⟩
  · apply certificate.entry other value
    simpa [List.getElem?_set, equal] using found

/-- The accepted entry's actual source-indexed write preserves all earlier
certificates and installs precisely its newly checked function. -/
theorem CompileEntryWitness.executable_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
    {env : metadata.Env} {sources : List funccode}
    (certificate : PartialExecutableModuleFunctions env sources before.functions.val)
    (typeIndex : U32) (source : funccode)
    (lookup : env.func_type_indices.val[w.entry.index.val]? = some typeIndex)
    (sourceLookup : sources[w.entry.index.val]? = some source)
    (code : DefinedExecutableFunctionCode env typeIndex source w.final.function) :
    PartialExecutableModuleFunctions env sources after.functions.val := by
  rw [w.published]
  simpa only [alloc.vec.Vec.set_val_eq] using certificate.set w.entry.index.val typeIndex w.final.function source lookup sourceLookup code

/-- Successful dense collection fills every slot, allowing the retained
per-index source witnesses to be assembled into the complete module list. -/
theorem PartialExecutableModuleFunctions.complete {env sources pending}
    (certificate : PartialExecutableModuleFunctions env sources pending)
    (functions : List runtime.bytecode.CompiledFunction)
    (collected : pending = functions.map some) :
    PendingExecutableModuleFunctions env pending sources := by
  have length : functions.length = env.func_type_indices.val.length := by
    simpa only [collected, List.length_map] using certificate.count
  refine ⟨certificate.sourceCount, ?_⟩
  intro index typeIndex lookup
  have bound : index < functions.length := by
    rw [length]
    exact (List.getElem?_eq_some_iff.mp lookup).1
  have found : pending[index]? = some (some functions[index]) := by simp [collected, bound]
  obtain ⟨actualType, source, actualLookup, sourceLookup, code⟩ := certificate.entry index functions[index] found
  have same : actualType = typeIndex := by simpa [lookup] using actualLookup.symm
  subst actualType
  exact ⟨functions[index], source, found, sourceLookup, code⟩
end Itasca.Compiler

end

/-! ## CompileExecutable -/

section

/-!
Executable-function certificates through entry compilation, scheduler submission and whole-module assembly. The final result retains source function ordering and each compiled body certificate.
-/

/-! ## Compile Entry Executable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The scheduler's actual entry construction, issued batch validation, and
finish establish the source-indexed function certificate. All compiler-state
premises are supplied by the checked entry proof. -/
theorem CompileEntryWitness.compile_executable {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : Stream.Batch.Issued} (reachable : Stream.Batch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    {finish : Usize}
    (entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
      w.initial w.final)
    {source : List instr} (encoded : Body.BodyEncoding entry.body source) :
    DefinedExecutableFunctionCode batch.env entry.typeIdx
      (.FUNC (.mk_uN entry.typeIdx.val)
        ((CodeEntry.Locals.declared entry.groups).map Translation.valueType |>.map local.LOCAL) source) w.final.function := by
  have certificate := witness_compile_executable ops law entry
    (signatures := before.signatures.deref) (functionSlots := before.func_param_slots.deref)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using signatureTable)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using functionTable)
    (w.end_fits reachable bounded origin entry) w.created encoded
    w.final.function w.final.budget w.finished
  simpa only [w.metadata.1] using certificate
end Itasca.Compiler

end

/-! ## Executable Compile Assembly -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileWitness.defined_executable_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingExecutableModuleFunctions w.env w.scheduler.functions.val sources) :
    ExecutableModuleFunctions executable sources ∧ InitializerMappings executable := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail w.functions) rfl
    (w.function_order law)
  obtain ⟨source, prefixCode, initializers⟩ := w.initializers law
  exact ⟨initialCode.extend source prefixCode, initializers⟩
end Itasca.Compiler

end

/-! ## Executable Compile Scheduler Assembly -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.initial_executable_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialExecutableModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialExecutableModuleFunctions.empty
  rw [source_functions_length (by rw [c.functions, c.codeCount]), c.functions]

/-- Once actual submission has filled the canonical ledger, the remaining
driver phases, collection and initializer lowering establish module coverage.
No further compiler relation or callback premise is required. -/
theorem CompileSourceCertificate.executable_functions_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialExecutableModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    ExecutableModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialExecutableModuleFunctions w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_executable_functions law (final.complete w.functions.val (w.function_order law))
end Itasca.Compiler

end

/-! ## Executable Scheduler Submission -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileEntries.executable_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    {env : metadata.Env} {sources : List funccode} {issued : Stream.Batch.Issued}
    (reachable : Stream.Batch.Reachable issued batch)
    (initial : PartialExecutableModuleFunctions env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.StreamingBatch),
      schedulerStatic current = schedulerStatic before → Stream.Batch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ DefinedExecutableFunctionCode env typeIndex source w.final.function) :
    PartialExecutableModuleFunctions env sources after.functions.val := by
  have result := run.fold
    (fun scheduler worker => schedulerStatic scheduler = schedulerStatic before ∧
      Stream.Batch.Reachable issued worker ∧ PartialExecutableModuleFunctions env sources scheduler.functions.val)
    ⟨rfl, reachable, initial⟩ ?_
  · exact result.2.2
  · intro current worker next nextWorker invariant w
    obtain ⟨typeIndex, source, lookup, sourceLookup, code⟩ := entries current next worker nextWorker invariant.1 invariant.2.1 w
    exact ⟨w.static.trans invariant.1, w.reachable invariant.2.1,
      w.executable_functions invariant.2.2 typeIndex source lookup sourceLookup code⟩

/-- Submission's queue push changes no function slot. The ledger after a
successful real batch therefore contains every previously checked entry and
each newly certified entry at its issued index. -/
theorem compiler_submit_executable_functions {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before after : runtime.compiler.CompileScheduler A)
    (issued : Stream.Batch.Issued) (env : metadata.Env) (sources : List funccode)
    (initial : PartialExecutableModuleFunctions env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.StreamingBatch),
      schedulerStatic current = schedulerStatic before → Stream.Batch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ DefinedExecutableFunctionCode env typeIndex source w.final.function)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before issued.seed = .ok (.Ok (), after)) :
    PartialExecutableModuleFunctions env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  obtain ⟨middle, worker, run, queue, same⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
  have certificates := run.executable_functions .seed initial entries
  rw [same]
  exact ⟨certificates, run.static⟩

theorem compiler_poll_executable_functions {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.StreamingBatch)
    {env : metadata.Env} {sources : List funccode} (initial : PartialExecutableModuleFunctions env sources before.functions.val)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    PartialExecutableModuleFunctions env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  rw [(compiler_poll_accepted allocator before after batch accepted).2]
  exact ⟨initial, rfl⟩
end Itasca.Compiler

end

/-! ## Source Compile Executable Entry -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A successful scheduler entry is paired with the original module's exact
source function using only source framing and the actual issued-worker history. -/
theorem CompileEntryWitness.compile_source_executable {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : Stream.Batch.Issued} (reachable : Stream.Batch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (bounds : CodeEntry.Bounds batch.env)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (raw : Binary.Module)
    (declarations : raw.functions = batch.env.func_type_indices.val)
    (prior taken remaining : List Binary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (first : issued.first_func.val = prior.length)
    (count : issued.num_funcs.val = taken.length)
    (encoded : Binary.Rep (CodeEntry.CodeEncoding) taken issued.code.val) :
    ∃ typeIndex source,
      batch.env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
      (sourceFunctions raw)[w.entry.index.val]? = some source ∧
      DefinedExecutableFunctionCode batch.env typeIndex source w.final.function := by
  obtain ⟨finish, indexEq, entry, typed⟩ := w.typed bounds
  have dispatched := Stream.Batch.Reachable.dispatch reachable w.dispatch
  have identity := dispatched.validation.1
  obtain ⟨_, _, envEq, codeEq, _, firstEq, countEq⟩ := identity
  have countBound : w.dispatched.num_validated.val < taken.length := by
    have cases := stream.StreamingBatch.validate_func.cases
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched finalBatch w.entry.index w.initial w.final (.Ok ()) w.validated
    rcases cases with ⟨error, _, impossible, _⟩ | ⟨_, error, _, impossible, _⟩ |
      ⟨_, finish, n, next, _⟩
    · cases impossible
    · cases impossible
    · have size := (stream.StreamingBatch.validate_next.accepted _ _ _ _ _ _ next).1
      simpa only [countEq, count] using size
  have entryBounds : CodeEntry.Bounds w.dispatched.env := by simpa only [w.metadata.1] using bounds
  obtain ⟨rawEntry, found, groups, body⟩ := witness_batch_source_lookup entry dispatched entryBounds encoded countBound
  have position : w.entry.index.val = prior.length + w.dispatched.num_validated.val := by
    have batchIdentity := reachable.validation.1
    have batchFirst := batchIdentity.2.2.2.2.2.1
    rw [indexEq, batchFirst, first, w.metadata.2.1]
  have rawFound : raw.codes[w.entry.index.val]? = some rawEntry := by
    rw [split, position]
    exact source_entry_offset found
  have rawMember : rawEntry ∈ raw.codes := List.mem_of_getElem? rawFound
  have typeFound : batch.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
    have found : w.dispatched.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
      simp only [List.getElem?_eq_getElem entry.index_lt, entry.index_type]
    simpa only [w.metadata.1] using found
  have certificate := w.compile_executable law reachable bounded origin signatureTable functionTable entry body
  refine ⟨entry.typeIdx, sourceFunctionCode entry.typeIdx rawEntry, typeFound,
    source_functions_lookup (by simpa only [declarations] using typeFound) rawFound, ?_⟩
  simpa only [sourceFunctionCode, Binary.Code.declared, CodeEntry.Locals.declared, groups, List.map_map, Function.comp_def] using certificate
end Itasca.Compiler

end

/-! ## Scheduler Executable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Captured module tables and the exact source-indexed certificate ledger
retained throughout actual eager compilation and worker retirement. -/
structure SchedulerExecutable {A : Type} (env : metadata.Env) (sources : List funccode)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType))
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  functions : PartialExecutableModuleFunctions env sources scheduler.functions.val

theorem SchedulerExecutable.transport {A : Type} {env sources}
    {before after : runtime.compiler.CompileScheduler A}
    (initial : SchedulerExecutable env sources before)
    (same : schedulerStatic after = schedulerStatic before)
    (functions : PartialExecutableModuleFunctions env sources after.functions.val) :
    SchedulerExecutable env sources after := by
  have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
      after.code_start = before.code_start := by simpa [schedulerStatic] using same
  exact ⟨by simpa only [fields.1] using initial.signatures,
    by simpa only [fields.2.1] using initial.functionSlots,
    by simpa only [fields.2.2] using initial.origin, functions⟩

/-- A submitted batch's real entry calls are certified against exactly its
independently decoded source slice. The entry and opcode theorems discharge
every compiler-correctness obligation internally. -/
theorem scheduler_batch_executable {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (env : metadata.Env) (raw : Binary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env)
    (before after : runtime.compiler.CompileScheduler A) (issued : Stream.Batch.Issued)
    (prior taken remaining : List Binary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (sameEnv : issued.env = env)
    (first : issued.first_func.val = prior.length) (count : issued.num_funcs.val = taken.length)
    (encoded : Binary.Rep (CodeEntry.CodeEncoding) taken issued.code.val)
    (bounded : issued.Bounded) (initial : SchedulerExecutable env (sourceFunctions raw) before)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      ops before issued.seed = .ok (.Ok (), after)) :
    SchedulerExecutable env (sourceFunctions raw) after := by
  have entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.StreamingBatch),
      schedulerStatic current = schedulerStatic before → Stream.Batch.Reachable issued worker →
      ∀ w : CompileEntryWitness ops current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          (sourceFunctions raw)[w.entry.index.val]? = some source ∧
          DefinedExecutableFunctionCode env typeIndex source w.final.function := by
    intro current next worker nextWorker static reachable w
    have fields : current.signatures = before.signatures ∧ current.func_param_slots = before.func_param_slots ∧
        current.code_start = before.code_start := by simpa [schedulerStatic] using static
    obtain ⟨_, _, workerEnv, _, _, _, _⟩ := reachable.validation.1
    have envEq : worker.env = env := workerEnv.trans sameEnv
    have certificate := w.compile_source_executable law reachable bounded
      (by simpa only [fields.2.2] using initial.origin)
      (by simpa only [envEq] using bounds)
      (by simpa only [fields.1, envEq] using initial.signatures)
      (by simpa only [fields.2.1, envEq] using initial.functionSlots)
      raw (by simpa only [envEq] using declarations) prior taken remaining split first count
      encoded
    simpa only [envEq] using certificate
  obtain ⟨functions, same⟩ := compiler_submit_executable_functions ops law before after issued env (sourceFunctions raw)
    initial.functions entries accepted
  exact initial.transport same functions

/-- The actual streaming submission loop establishes certificates for every
populated slot of the original module source list. No callback, body relation,
or independently supplied compiler certificate is a premise. -/
theorem compiler_submit_source_executable_functions {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (source : stream.StreamingSource S) (state : S) (moduleId : U64)
    (env : metadata.Env) (code : Slice U8) (config : stream.StreamingConfig)
    (raw : Binary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env)
    (environment tail : List U8) (available : Stream.Source.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize)
    (encoded : Binary.At (Binary.Rep (CodeEntry.CodeEncoding)) code start raw.codes (Slice.len code))
    (count : raw.codes.length = env.func_type_indices.val.length)
    (before after : runtime.compiler.CompileScheduler A) (pending : alloc.vec.Vec Usize)
    (initial : SchedulerExecutable env (sourceFunctions raw) before)
    (accepted : stream.submit_code_batches source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      moduleId state env (Slice.len code) start config before = .ok (.Ok pending, after)) :
    SchedulerExecutable env (sourceFunctions raw) after := by
  apply SourceSubmission.submit source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    state moduleId env code config raw.codes (SchedulerExecutable env (sourceFunctions raw))
    environment tail available capacity start encoded count ?_ ?_ before after pending initial accepted
  · intro current next issued prior taken remaining split moduleEq sameEnv first counted encoded bounded ready accepted
    exact scheduler_batch_executable ops law env raw declarations bounds current next issued
      prior taken remaining split sameEnv first counted encoded bounded ready accepted
  · intro current next worker ready accepted
    obtain ⟨functions, same⟩ := compiler_poll_executable_functions ops current next worker ready.functions accepted
    exact ready.transport same functions
end Itasca.Compiler

end

/-! ## Compile Executable -/

section

/-! Source-ordered executable certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.executable_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    ExecutableModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  obtain ⟨signatures,slots,origin⟩ := c.scheduler_setup law
  have initial : SchedulerExecutable w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨signatures, slots, origin, c.initial_executable_functions law⟩
  have submitted := c.run.remaining.submit_call
  rw [c.code_length] at submitted
  have certified := compiler_submit_source_executable_functions ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code c.run.remaining.config c.raw c.functions c.entryBounds
    c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.executable_functions_of_submission law certified.functions

/-- Public successful compilation produces
source-ordered certificates for the exact canonical module syntax. -/
theorem compile_executable_functions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    ∃ raw, Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) raw bytes.val ∧
      Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw) ∧
      Module.Elaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (Module.Elaboration.moduleOf raw) ∧ Module.Elaboration.Restrictions raw ∧
      Module.Elaboration.AccessorTypes executable.module.env raw ∧
      ExecutableModuleFunctions executable (sourceFunctions raw) ∧ InitializerMappings executable := by
  obtain ⟨w⟩ := compile_accepted ops bytes limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.executable_functions law
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := Binary.Source.rawModuleInjective (WebAssembly.Binary.ModuleEncoding.unique encoded
    (Binary.Source.moduleEncoding c.encoded))
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    certificates.1, certificates.2⟩
end Itasca.Compiler

end

end

end

/-! ## InitializerCompilationAvailable -/

section

/-!
Proofs for Runtime / Compiler / Module.

This module collects InitializerCompilationAvailable, CompileExecutableCapacities.
Each section documents its contracts and consumers.
-/

/-! ## InitializerCompilationAvailable -/

section

open Itasca.Representation

/-! ## SegmentCompilationAvailable -/

section

/-!
Successful data/element segment compilation from bounded segment demand. Per-segment emission and their folds establish the final segment compilation availability theorem.
-/

/-! ## Initializer Emit Data Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Data-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_data_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Data)
    (lookup : module.module.tail.data.val[index.val]? = some segment)
    (typed : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val)
    (capacity : function.code.length + 5 ≤ Usize.max) (request : function.code.length + 5 ≤ bound)
    (indexBound : index.val ≤ U32.max) (lengthBound : segment.init.length ≤ U32.max) :
    runtime.compiler.initialize.emit_data ops module budget function index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val ≤ budget.instructions.val + 5 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.code.length ≤ function.code.length + 5 ∧
      out.2.2.v128_pool = function.v128_pool ∧ out.2.2.indirect = function.indirect ⦄ := by
  exact runtime.compiler.initialize.emit_data.available ops bound available module budget function index segment
    ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound⟩

end Itasca.Compiler

end

/-! ## Initializer Emit Datas Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The full source-ordered data bytecode loop accepts with five emitted
instructions per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_datas_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.tail.data.val.length)
    (sourceCount : module.module.tail.data.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.tail.data.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.tail.data.val.length-index.val) ≤ bound) :
    runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
      out.2.2.indirect = function.indirect ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  let P := fun (charged : runtime.compiler.Budget A) (current : runtime.bytecode.CompiledFunction) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    charged.instructions.val + 5*(module.module.tail.data.val.length-cursor.val) ≤
      budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
    current.code.length + 5*(module.module.tail.data.val.length-cursor.val) ≤
      function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
    current.indirect = function.indirect ∧ current.v128_pool = function.v128_pool
  change WP.spec (loop (initializerEmitDataLoop ops module).body (budget, index, .Ok (), function)) _
  apply InitializerSegmentLoop.available
    { rules := initializerEmitDataLoop ops module, budget := budget, function := function, index := index, bounded := inside,
      P := P, Q := fun charged after => charged.limits = budget.limits ∧
        charged.instructions.val ≤ budget.instructions.val + 5*(module.module.tail.data.val.length-index.val) ∧
        after.code.length ≤ function.code.length + 5*(module.module.tail.data.val.length-index.val) ∧
        after.indirect = function.indirect ∧ after.v128_pool = function.v128_pool,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor position prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val < module.module.tail.data.val.length at position
    let segment := module.module.tail.data.val[cursor.val]'position
    have lookup : module.module.tail.data.val[cursor.val]? = some segment := List.getElem?_eq_getElem position
    apply WP.spec_mono (initializer_emit_data_available ops bound available module charged current cursor segment lookup
      (typed segment (List.getElem_mem position)) (by rw [limits]; omega) (by omega) (by omega)
      (by change module.module.tail.data.val.length ≤ U32.max at sourceCount; omega)
      (sourceLengths segment (List.getElem_mem position)))
    rintro ⟨result, nextBudget, next⟩ ⟨accepted, usedAgain, limitsAgain, codeAgain, poolAgain, pairsAgain⟩
    dsimp only at accepted usedAgain limitsAgain codeAgain poolAgain pairsAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega,
      pairsAgain.trans pairs, poolAgain.trans pool⟩
  · intro charged current cursor last prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val = module.module.tail.data.val.length at last
    exact ⟨limits, by omega, by omega, pairs, pool⟩
  · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

end Itasca.Compiler

end

/-! ## Initializer Emit Element Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Element-segment bytecode emission accepts from source offset typing and a
conservative five-instruction demand. Source indices have independent u32 bounds. -/
theorem initializer_emit_element_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val)
    (capacity : function.code.length + 5 ≤ Usize.max) (request : function.code.length + 5 ≤ bound)
    (indexBound : index.val ≤ U32.max) (lengthBound : segment.init.length ≤ U32.max)
    (pairIndex : function.indirect.length ≤ U32.max)
    (pairCapacity : function.indirect.length < Usize.max)
    (pairReserve : function.indirect.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit_element ops module budget function index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val ≤ budget.instructions.val + 5 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.code.length ≤ function.code.length + 5 ∧
      out.2.2.v128_pool = function.v128_pool ∧ out.2.2.indirect.length ≤ function.indirect.length + 1 ⦄ := by
  exact runtime.compiler.initialize.emit_element.available ops bound available module budget function index segment
    ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound, pairIndex, pairCapacity, pairReserve⟩

end Itasca.Compiler

end

/-! ## Initializer Emit Elements Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The full source-ordered element bytecode loop accepts with five emitted
instructions and one descriptor per remaining source segment as conservative
demand. Offset literals require no pool allocation. -/
theorem initializer_emit_elements_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ module.module.env.elements.val.length)
    (sourceCount : module.module.env.elements.length ≤ U32.max)
    (sourceLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max)
    (typed : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (instructions : budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ≤
      budget.limits.max_instructions.val)
    (codeCapacity : function.code.length + 5*(module.module.env.elements.val.length-index.val) ≤ Usize.max)
    (codeReserve : function.code.length + 5*(module.module.env.elements.val.length-index.val) ≤ bound)
    (pairCapacity : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ Usize.max)
    (pairReserve : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ bound)
    (pairWord : function.indirect.length + (module.module.env.elements.val.length-index.val) ≤ U32.max) :
    runtime.compiler.initialize.lower_loop3 ops module budget index (.Ok ()) function ⦃ out =>
      out.2.1 = .Ok () ∧ out.1.limits = budget.limits ∧
      out.1.instructions.val ≤ budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
      out.2.2.code.length ≤ function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
      out.2.2.indirect.length ≤ function.indirect.length + (module.module.env.elements.val.length-index.val) ∧
      out.2.2.v128_pool = function.v128_pool ⦄ := by
  let P := fun (charged : runtime.compiler.Budget A) (current : runtime.bytecode.CompiledFunction) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    charged.instructions.val + 5*(module.module.env.elements.val.length-cursor.val) ≤
      budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
    current.code.length + 5*(module.module.env.elements.val.length-cursor.val) ≤
      function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
    current.indirect.length + (module.module.env.elements.val.length-cursor.val) ≤
      function.indirect.length + (module.module.env.elements.val.length-index.val) ∧ current.v128_pool = function.v128_pool
  change WP.spec (loop (initializerEmitElementLoop ops module).body (budget, index, .Ok (), function)) _
  apply InitializerSegmentLoop.available
    { rules := initializerEmitElementLoop ops module, budget := budget, function := function, index := index, bounded := inside,
      P := P, Q := fun charged after => charged.limits = budget.limits ∧
        charged.instructions.val ≤ budget.instructions.val + 5*(module.module.env.elements.val.length-index.val) ∧
        after.code.length ≤ function.code.length + 5*(module.module.env.elements.val.length-index.val) ∧
        after.indirect.length ≤ function.indirect.length + (module.module.env.elements.val.length-index.val) ∧ after.v128_pool = function.v128_pool,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor position prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val < module.module.env.elements.val.length at position
    let segment := module.module.env.elements.val[cursor.val]'position
    have lookup : module.module.env.elements.val[cursor.val]? = some segment := List.getElem?_eq_getElem position
    apply WP.spec_mono (initializer_emit_element_available ops bound available module charged current cursor segment lookup
      (typed segment (List.getElem_mem position)) (by rw [limits]; omega) (by omega) (by omega)
      (by change module.module.env.elements.val.length ≤ U32.max at sourceCount; omega)
      (sourceLengths segment (List.getElem_mem position)) (by omega) (by omega) (by omega))
    rintro ⟨result, nextBudget, next⟩ ⟨accepted, usedAgain, limitsAgain, codeAgain, poolAgain, pairsAgain⟩
    dsimp only at accepted usedAgain limitsAgain codeAgain poolAgain pairsAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega,
      by omega, poolAgain.trans pool⟩
  · intro charged current cursor last prior
    obtain ⟨limits, used, code, pairs, pool⟩ := prior
    change cursor.val = module.module.env.elements.val.length at last
    exact ⟨limits, by omega, by omega, by omega, pool⟩
  · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, rfl⟩

end Itasca.Compiler

end

/-! ## Segment Compilation Available -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

def segmentCompilationDemand (module : runtime.compiler.ExecutableModule) : Nat :=
  5*(module.module.env.elements.val.length+module.module.tail.data.val.length)+1

/-- Source-derived requests for the generated segment program. The existing
function vector and native per-request allocation bound are accounted separately. -/
structure SegmentCompilationDemand {A : Type} (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (bound : Nat) : Prop where
  instructions : budget.instructions.val + segmentCompilationDemand module ≤ budget.limits.max_instructions.val
  codeCapacity : segmentCompilationDemand module ≤ Usize.max
  codeReserve : segmentCompilationDemand module ≤ bound
  functionsCapacity : module.functions.length < Usize.max
  functionsReserve : module.functions.length+1 ≤ bound
  elementCount : module.module.env.elements.length ≤ U32.max
  dataCount : module.module.tail.data.length ≤ U32.max
  elementLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max
  dataLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max

/-- The complete extracted segment suffix accepts from source typing and
independent numerical demand. The program certificate and checker result are
constructed before publication, not supplied as compiler-success premises. -/
theorem segment_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (demand : SegmentCompilationDemand module budget bound)
    (elementsTyped : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32)
    (datasTyped : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32) :
    segmentCompilation ops module budget ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.module = module.module ∧ out.2.2.limits = budget.limits ∧
      out.2.2.instructions.val ≤ budget.instructions.val+segmentCompilationDemand module ⦄ := by
  let seed := {initializerSeed .I32 with slot_count := 0#u32}
  have seedEq : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed := rfl
  have instructionRoom := demand.instructions
  have codeCapacity := demand.codeCapacity
  have codeReserve := demand.codeReserve
  simp only [segmentCompilationDemand] at instructionRoom codeCapacity codeReserve
  obtain ⟨⟨b1,status,first⟩,firstCall,accepted,limits1,used1,code1,pairs1,pool1⟩ := WP.spec_imp_exists
    (initializer_emit_elements_available ops bound available module budget seed 0#usize (by simp)
      demand.elementCount demand.elementLengths elementsTyped
      (by simpa [seed,initializerSeed] using (show budget.instructions.val+
        5*module.module.env.elements.val.length ≤ budget.limits.max_instructions.val by omega))
      (by simp [seed,initializerSeed] <;> omega) (by simp [seed,initializerSeed] <;> omega)
      (by simp [seed,initializerSeed] <;> omega) (by simp [seed,initializerSeed] <;> omega)
      (by simpa [seed,initializerSeed] using demand.elementCount))
  dsimp only at accepted limits1 used1 code1 pairs1 pool1
  subst status
  simp [seed,initializerSeed] at used1 code1 pairs1
  obtain ⟨elements,elementPrefix⟩ := element_program_loop ops law module seed seed first budget b1 0#usize []
    (.empty module seed) (by simp) elementsTyped firstCall
  obtain ⟨⟨b2,status,second⟩,secondCall,accepted,limits2,used2,code2,pairs2,pool2⟩ := WP.spec_imp_exists
    (initializer_emit_datas_available ops bound available module b1 first 0#usize (by simp)
      demand.dataCount demand.dataLengths datasTyped (by rw [limits1]; simp <;> omega)
      (by simp <;> omega) (by simp <;> omega))
  dsimp only at accepted limits2 used2 code2 pairs2 pool2
  subst status
  simp at used2 code2
  obtain ⟨datas,dataPrefix⟩ := data_program_loop ops law module first first second b1 b2 0#usize []
    (.empty module first) (by simp) datasTyped secondCall
  obtain ⟨⟨status,b3,finalCode⟩,emitCall,accepted,used3,limits3,appended⟩ := WP.spec_imp_exists
    (initializer_emit_available ops bound available b2 second.code (.Return 0#u32 0#u32)
      (by rw [limits2,limits1]; omega)
      (by change second.code.val.length < Usize.max; omega)
      (by change second.code.val.length + 1 ≤ bound; omega))
  dsimp only at accepted used3 limits3 appended
  subst status
  have program := segment_program_finish module seed first second finalCode elements datas elementPrefix dataPrefix
    appended (by simp [seed,initializerSeed]) (by simp [seed,initializerSeed]) rfl rfl rfl
  have metadata : second.body_start = 0#usize ∧ second.body_end = 0#usize ∧
      second.source_offsets.val = [] ∧ second.jump_tables.val = [] ∧ second.controls.val = [] := by
    rw [dataPrefix.fields,elementPrefix.fields]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨valid,checkCall,rfl⟩ := WP.spec_imp_exists
    (segment_program_well_formed program elementsTyped datasTyped metadata.1 metadata.2.1
      metadata.2.2.1 metadata.2.2.2.1 metadata.2.2.2.2)
  unfold segmentCompilation
  rw [seedEq,bind_ok,firstCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [secondCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [emitCall]
  simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [checkCall]
  simp only [bind_ok,↓reduceIte]
  step with budget_push_available ops bound available b3 module.functions {second with code := finalCode}
    demand.functionsCapacity demand.functionsReserve
    as ⟨status,afterBudget,functions,accepted,sameBudget,appendedFunctions⟩
  refine ⟨accepted,?_,?_⟩
  · simpa [sameBudget,limits3,limits2] using limits1
  · simp only [sameBudget]
    unfold segmentCompilationDemand
    omega

end Itasca.Compiler

end

end

/-! ## InitializerCompilationAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Independent constant-expression judgments for every source initializer. -/
structure InitializerSourceTyping (module : runtime.compiler.ExecutableModule) : Prop where
  globals : ∀ global ∈ module.module.env.globals.val,
    Itasca.Module.Constants.Valid module.module.env global.init global.gtype.valtype
  elements : ∀ segment ∈ module.module.env.elements.val, ∀ expr ∈ segment.init.val,
    Itasca.Module.Constants.Valid module.module.env expr (Itasca.Module.Constants.referenceValueType segment.elem)
  elementOffsets : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
    segment.mode = .Active table offset → Itasca.Module.Constants.Valid module.module.env offset .I32
  dataOffsets : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
    segment.mode = .Active memory offset → Itasca.Module.Constants.Valid module.module.env offset .I32

/-- The existing independent environment and data judgments discharge every
initializer typing premise; no emitted code or compiler observation is needed. -/
theorem InitializerSourceTyping.of_valid {module : runtime.compiler.ExecutableModule}
     (valid : Itasca.Module.Environment.Valid module.module.env)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, Itasca.Module.Data.Valid module.module.env segment) :
    InitializerSourceTyping module := by
  refine ⟨valid.globals,?_,?_,?_⟩
  · intro segment member
    exact (valid.elements segment member).2
  · intro segment member table offset mode
    have active := (valid.elements segment member).1
    rw [mode] at active
    exact active.choose_spec.2
  · intro segment member memory offset mode
    have active := dataValid segment member
    unfold Itasca.Module.Data.Valid at active
    rw [mode] at active
    exact active.2

/-- Conservative complete-pass demand, computed from source initializer counts
and existing retained vectors. Temporary element indices are included. -/
structure InitializerCompilationDemand {A : Type} (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (bound : Nat) : Prop where
  instructions : budget.instructions.val + 2*initializerMappingCost module.module + segmentCompilationDemand module ≤
    budget.limits.max_instructions.val
  mappingCapacity : initializerSize module + initializerMappingCost module.module + 1 ≤ Usize.max
  mappingReserve : initializerSize module + initializerMappingCost module.module + 1 ≤ bound
  literalReserve : 2 ≤ bound
  codeCapacity : segmentCompilationDemand module ≤ Usize.max
  codeReserve : segmentCompilationDemand module ≤ bound
  elementCount : module.module.env.elements.length ≤ U32.max
  dataCount : module.module.tail.data.length ≤ U32.max
  elementLengths : ∀ segment ∈ module.module.env.elements.val, segment.init.length ≤ U32.max
  dataLengths : ∀ segment ∈ module.module.tail.data.val, segment.init.length ≤ U32.max

/-- The real complete initializer pass accepts from independent source typing
and bounded allocation demand. Its emitted code, checker acceptance, and normal
return are established internally, not assumed as a trace or certificate. -/
theorem initializer_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (source : InitializerSourceTyping module) (demand : InitializerCompilationDemand module budget bound) :
    runtime.compiler.initialize.lower ops module budget ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.module = module.module ∧ out.2.2.limits = budget.limits ∧
      out.2.2.instructions.val ≤ budget.instructions.val + 2*initializerMappingCost module.module +
        segmentCompilationDemand module ⦄ := by
  have room := demand.instructions
  have capacity := demand.mappingCapacity
  have reserve := demand.mappingReserve
  unfold initializerMappingCost at room capacity reserve
  obtain ⟨⟨m1,b1,status⟩,call1,accepted,source1,size1,used1,limits1⟩ := WP.spec_imp_exists
    (initializer_globals_available ops bound available module budget 0#usize (by simp) source.globals
      (by simp; omega) demand.literalReserve (by simp; omega) (by simp; omega))
  dsimp only at accepted source1 size1 used1 limits1
  subst status
  simp only [show (0#usize).val = 0 from rfl,Nat.sub_zero] at size1 used1
  obtain ⟨⟨m2,b2,status⟩,call2,accepted,source2,limits2,size2,used2⟩ := WP.spec_imp_exists
    (initializer_elements_available ops bound available m1 b1 0#usize (by simp)
      (by simpa [source1] using source.elements) (by simpa [source1] using source.elementOffsets)
      (by rw [limits1]; simp [source1]; omega) demand.literalReserve
      (by simp [source1]; omega) (by simp [source1]; omega))
  dsimp only at accepted source2 limits2 size2 used2
  subst status
  have same2 : m2.module = module.module := source2.trans source1
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero,source1] at size2 used2
  obtain ⟨⟨m3,b3,status⟩,call3,accepted,source3,size3,used3,limits3⟩ := WP.spec_imp_exists
    (initializer_data_offsets_available ops bound available m2 b2 0#usize (by simp)
      (by simpa [same2] using source.dataOffsets)
      (by rw [limits2,limits1]; simp [same2]; omega) demand.literalReserve
      (by simp [same2]; omega) (by simp [same2]; omega))
  dsimp only at accepted source3 size3 used3 limits3
  subst status
  have same3 : m3.module = module.module := source3.trans same2
  simp only [show (0#usize).val = 0 from rfl,Nat.sub_zero,same2] at size3 used3
  have functions : m3.functions.length ≤ initializerSize m3 := by
    simp only [initializerSize,alloc.vec.Vec.length]
    omega
  have suffixDemand : SegmentCompilationDemand m3 b3 bound := by
    constructor
    · rw [limits3,limits2,limits1]
      simp only [segmentCompilationDemand,same3] at *
      omega
    · simpa [segmentCompilationDemand,same3] using demand.codeCapacity
    · simpa [segmentCompilationDemand,same3] using demand.codeReserve
    · omega
    · omega
    · simpa [same3] using demand.elementCount
    · simpa [same3] using demand.dataCount
    · simpa [same3] using demand.elementLengths
    · simpa [same3] using demand.dataLengths
  refine WP.spec_mono (runtime.compiler.initialize.lower.available ops module budget
    ⟨m1, m2, m3, b1, b2, b3, call1, call2, call3⟩
    (fun status after afterBudget => status = .Ok () ∧ after.module = module.module ∧ afterBudget.limits = budget.limits ∧
      afterBudget.instructions.val ≤ budget.instructions.val + 2*initializerMappingCost module.module + segmentCompilationDemand module)
    ?_) ?_
  · change segmentCompilation ops m3 b3 ⦃ out => _ ⦄
    apply WP.spec_mono (segment_compilation_available ops law bound available m3 b3 suffixDemand
      (by simpa [same3] using source.elementOffsets) (by simpa [same3] using source.dataOffsets))
    rintro ⟨status, after, afterBudget⟩ post
    dsimp only at post ⊢
    refine ⟨post.1,post.2.1.trans same3,?_,?_⟩
    · exact post.2.2.1.trans (limits3.trans (limits2.trans limits1))
    · have suffixUsed := post.2.2.2
      simp only [segmentCompilationDemand,same3] at suffixUsed ⊢
      unfold initializerMappingCost
      omega

  · rintro ⟨status, after, afterBudget⟩ post
    exact post

end Itasca.Compiler

end

end

/-! ## CompileExecutableCapacities -/

section

open Itasca.Representation

/-!
Source-derived frame capacities through compiler entry, scheduler submission and module assembly. The resulting certificate relates issued compiled functions to independent source demand.
-/

/-! ## Capacity Assembly -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Initializer lowering appends synthetic functions without changing any
source function's retained frame-capacity bound. -/
theorem CompileWitness.defined_capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingModuleCapacities w.env w.scheduler.functions.val sources) :
    ModuleCapacities executable sources := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail w.functions) rfl
    (w.function_order law)
  obtain ⟨source, prefixCode, _⟩ := w.initializers law
  exact initialCode.extend source prefixCode

theorem CompileSourceCertificate.initial_capacities {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialModuleCapacities w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialModuleCapacities.empty
  rw [source_functions_length (by rw [c.functions, c.codeCount]), c.functions]

theorem CompileSourceCertificate.capacities_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialModuleCapacities w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    ModuleCapacities executable (sourceFunctions c.raw) := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialModuleCapacities w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_capacities law (final.complete w.functions.val (w.function_order law))
end Itasca.Compiler

end

/-! ## Capacity Submission -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual batch run preserves the per-index ledger once its actual entry
witnesses have been certified. Reachability and fixed metadata are supplied to
the entry proof, rather than assumed again for each arbitrary worker. -/
theorem CompileEntries.capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (run : CompileEntries allocator before batch after finalBatch)
     {env : metadata.Env} {sources : List funccode} {issued : Stream.Batch.Issued}
    (reachable : Stream.Batch.Reachable issued batch)
    (initial : PartialModuleCapacities env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.StreamingBatch),
      schedulerStatic current = schedulerStatic before → Stream.Batch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ Representation.CompiledFunctionCapacity env typeIndex source w.final.function) :
    PartialModuleCapacities env sources after.functions.val := by
  have result := run.fold
    (fun scheduler worker => schedulerStatic scheduler = schedulerStatic before ∧
      Stream.Batch.Reachable issued worker ∧ PartialModuleCapacities env sources scheduler.functions.val)
    ⟨rfl, reachable, initial⟩ ?_
  · exact result.2.2
  · intro current worker next nextWorker invariant w
    obtain ⟨typeIndex, source, lookup, sourceLookup, code⟩ := entries current next worker nextWorker invariant.1 invariant.2.1 w
    exact ⟨w.static.trans invariant.1, w.reachable invariant.2.1,
      w.capacities invariant.2.2 typeIndex source lookup sourceLookup code⟩

/-- Submission's queue push changes no function slot. The ledger after a
successful real batch therefore contains every previously checked entry and
each newly certified entry at its issued index. -/
theorem compiler_submit_capacities {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before after : runtime.compiler.CompileScheduler A)
    (issued : Stream.Batch.Issued) (env : metadata.Env) (sources : List funccode)
    (initial : PartialModuleCapacities env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.StreamingBatch),
      schedulerStatic current = schedulerStatic before → Stream.Batch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ Representation.CompiledFunctionCapacity env typeIndex source w.final.function)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before issued.seed = .ok (.Ok (), after)) :
    PartialModuleCapacities env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  obtain ⟨middle, worker, run, queue, same⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
  have certificates := run.capacities .seed initial entries
  rw [same]
  exact ⟨certificates, run.static⟩

theorem compiler_poll_capacities {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.StreamingBatch)
     {env : metadata.Env} {sources : List funccode} (initial : PartialModuleCapacities env sources before.functions.val)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    PartialModuleCapacities env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  rw [(compiler_poll_accepted allocator before after batch accepted).2]
  exact ⟨initial, rfl⟩
end Itasca.Compiler

end

/-! ## Executable Compile Entry Capacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The scheduler's actual entry construction, issued batch validation, and
finish establish the source-indexed capacity certificate. All compiler-state
premises are supplied by the checked entry proof. -/
theorem CompileEntryWitness.compile_executable_capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops) (envLimits : CodeEntry.EnvironmentWithinLimits batch.env)
    {issued : Stream.Batch.Issued} (reachable : Stream.Batch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    {finish : Usize}
    (entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
      w.initial w.final)
    {source : List instr} (encoded : Body.BodyEncoding entry.body source) :
    Representation.CompiledFunctionCapacity batch.env entry.typeIdx
      (.FUNC (.mk_uN entry.typeIdx.val)
        ((CodeEntry.Locals.declared entry.groups).map Translation.valueType |>.map local.LOCAL) source) w.final.function := by
  have certificate := witness_executable_function_capacity ops law
    (by simpa only [w.metadata.1] using envLimits) entry
    (signatures := before.signatures.deref) (functionSlots := before.func_param_slots.deref)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using signatureTable)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using functionTable)
    (w.end_fits reachable bounded origin entry) w.created encoded
    w.final.function w.final.budget w.finished
  simpa only [w.metadata.1] using certificate
/-- A successful scheduler entry is paired with the original module's exact
source function using only source framing and the actual issued-worker history. -/
theorem CompileEntryWitness.compile_executable_source_capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : Stream.Batch.Issued} (reachable : Stream.Batch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (bounds : CodeEntry.Bounds batch.env)
    (envLimits : CodeEntry.EnvironmentWithinLimits batch.env)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (raw : Binary.Module)
    (declarations : raw.functions = batch.env.func_type_indices.val)
    (prior taken remaining : List Binary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (first : issued.first_func.val = prior.length)
    (count : issued.num_funcs.val = taken.length)
    (encoded : Binary.Rep (CodeEntry.CodeEncoding) taken issued.code.val) :
    ∃ typeIndex source,
      batch.env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
      (sourceFunctions raw)[w.entry.index.val]? = some source ∧
      Representation.CompiledFunctionCapacity batch.env typeIndex source w.final.function := by
  obtain ⟨finish, indexEq, entry, typed⟩ := w.typed bounds
  have dispatched := Stream.Batch.Reachable.dispatch reachable w.dispatch
  have identity := dispatched.validation.1
  obtain ⟨_, _, envEq, codeEq, _, firstEq, countEq⟩ := identity
  have countBound : w.dispatched.num_validated.val < taken.length := by
    have cases := stream.StreamingBatch.validate_func.cases
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched finalBatch w.entry.index w.initial w.final (.Ok ()) w.validated
    rcases cases with ⟨error, _, impossible, _⟩ | ⟨_, error, _, impossible, _⟩ |
      ⟨_, finish, n, next, _⟩
    · cases impossible
    · cases impossible
    · have size := (stream.StreamingBatch.validate_next.accepted _ _ _ _ _ _ next).1
      simpa only [countEq, count] using size
  have entryBounds : CodeEntry.Bounds w.dispatched.env := by simpa only [w.metadata.1] using bounds
  obtain ⟨rawEntry, found, groups, body⟩ := witness_batch_source_lookup entry dispatched entryBounds encoded countBound
  have position : w.entry.index.val = prior.length + w.dispatched.num_validated.val := by
    have batchIdentity := reachable.validation.1
    have batchFirst := batchIdentity.2.2.2.2.2.1
    rw [indexEq, batchFirst, first, w.metadata.2.1]
  have rawFound : raw.codes[w.entry.index.val]? = some rawEntry := by
    rw [split, position]
    exact source_entry_offset found
  have rawMember : rawEntry ∈ raw.codes := List.mem_of_getElem? rawFound
  have typeFound : batch.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
    have found : w.dispatched.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
      simp only [List.getElem?_eq_getElem entry.index_lt, entry.index_type]
    simpa only [w.metadata.1] using found
  have certificate := w.compile_executable_capacity law envLimits reachable bounded origin signatureTable functionTable entry body

  refine ⟨entry.typeIdx, sourceFunctionCode entry.typeIdx rawEntry, typeFound,
    source_functions_lookup (by simpa only [declarations] using typeFound) rawFound, ?_⟩
  simpa only [sourceFunctionCode, Binary.Code.declared, CodeEntry.Locals.declared, groups, List.map_map, Function.comp_def] using certificate
end Itasca.Compiler

end

/-! ## Scheduler Capacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Captured module tables and the exact source-indexed certificate ledger
retained throughout actual eager compilation and worker retirement. -/
structure SchedulerCapacity {A : Type} (env : metadata.Env) (sources : List funccode)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType))
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  functions : PartialModuleCapacities env sources scheduler.functions.val

theorem SchedulerCapacity.transport {A : Type} {env sources}
    {before after : runtime.compiler.CompileScheduler A}
    (initial : SchedulerCapacity env sources before)
    (same : schedulerStatic after = schedulerStatic before)
    (functions : PartialModuleCapacities env sources after.functions.val) :
    SchedulerCapacity env sources after := by
  have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
      after.code_start = before.code_start := by simpa [schedulerStatic] using same
  exact ⟨by simpa only [fields.1] using initial.signatures,
    by simpa only [fields.2.1] using initial.functionSlots,
    by simpa only [fields.2.2] using initial.origin, functions⟩

end Itasca.Compiler

end

/-! ## Executable Scheduler Capacity -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A submitted batch's real entry calls are certified against exactly its
independently decoded source slice. The entry and opcode theorems discharge
every compiler-correctness obligation internally. -/
theorem scheduler_batch_executable_capacity {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (env : metadata.Env) (raw : Binary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env) (envLimits : CodeEntry.EnvironmentWithinLimits env)
    (before after : runtime.compiler.CompileScheduler A) (issued : Stream.Batch.Issued)
    (prior taken remaining : List Binary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (sameEnv : issued.env = env)
    (first : issued.first_func.val = prior.length) (count : issued.num_funcs.val = taken.length)
    (encoded : Binary.Rep (CodeEntry.CodeEncoding) taken issued.code.val)
    (bounded : issued.Bounded) (initial : SchedulerCapacity env (sourceFunctions raw) before)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      ops before issued.seed = .ok (.Ok (), after)) :
    SchedulerCapacity env (sourceFunctions raw) after := by
  have entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.StreamingBatch),
      schedulerStatic current = schedulerStatic before → Stream.Batch.Reachable issued worker →
      ∀ w : CompileEntryWitness ops current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          (sourceFunctions raw)[w.entry.index.val]? = some source ∧
          Representation.CompiledFunctionCapacity env typeIndex source w.final.function := by
    intro current next worker nextWorker static reachable w
    have fields : current.signatures = before.signatures ∧ current.func_param_slots = before.func_param_slots ∧
        current.code_start = before.code_start := by simpa [schedulerStatic] using static
    obtain ⟨_, _, workerEnv, _, _, _, _⟩ := reachable.validation.1
    have envEq : worker.env = env := workerEnv.trans sameEnv
    have certificate := w.compile_executable_source_capacity law reachable bounded
      (by simpa only [fields.2.2] using initial.origin)
      (by simpa only [envEq] using bounds)
      (by simpa only [envEq] using envLimits)
      (by simpa only [fields.1, envEq] using initial.signatures)
      (by simpa only [fields.2.1, envEq] using initial.functionSlots)
      raw (by simpa only [envEq] using declarations) prior taken remaining split first count
      encoded
    simpa only [envEq] using certificate
  obtain ⟨functions, same⟩ := compiler_submit_capacities ops law before after issued env (sourceFunctions raw)
    initial.functions entries accepted
  exact initial.transport same functions

/-- The actual streaming submission loop establishes certificates for every
populated slot of the original module source list. No callback, body relation,
or independently supplied compiler certificate is a premise. -/
theorem compiler_submit_executable_source_capacities {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (source : stream.StreamingSource S) (state : S) (moduleId : U64)
    (env : metadata.Env) (code : Slice U8) (config : stream.StreamingConfig)
    (raw : Binary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env) (envLimits : CodeEntry.EnvironmentWithinLimits env)
    (environment tail : List U8) (available : Stream.Source.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize)
    (encoded : Binary.At (Binary.Rep (CodeEntry.CodeEncoding)) code start raw.codes (Slice.len code))
    (count : raw.codes.length = env.func_type_indices.val.length)
    (before after : runtime.compiler.CompileScheduler A) (pending : alloc.vec.Vec Usize)
    (initial : SchedulerCapacity env (sourceFunctions raw) before)
    (accepted : stream.submit_code_batches source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      moduleId state env (Slice.len code) start config before = .ok (.Ok pending, after)) :
    SchedulerCapacity env (sourceFunctions raw) after := by
  apply SourceSubmission.submit source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    state moduleId env code config raw.codes (SchedulerCapacity env (sourceFunctions raw))
    environment tail available capacity start encoded count ?_ ?_ before after pending initial accepted
  · intro current next issued prior taken remaining split moduleEq sameEnv first counted encoded bounded ready accepted
    exact scheduler_batch_executable_capacity ops law env raw declarations bounds envLimits current next issued
      prior taken remaining split sameEnv first counted encoded bounded ready accepted
  · intro current next worker ready accepted
    obtain ⟨functions, same⟩ := compiler_poll_capacities ops current next worker ready.functions accepted
    exact ready.transport same functions
end Itasca.Compiler

end

/-! ## Compile Executable Capacities -/

section

/-! Source-ordered executablecapacities certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual successful compilation establishes all defined-function source
certificates for the complete independently encoded module. The scheduler,
reader, compiler callbacks and final assembly are discharged internally. -/
theorem CompileSourceCertificate.executable_capacities {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    ModuleCapacities executable (sourceFunctions c.raw) := by
  obtain ⟨signatures,slots,origin⟩ := c.scheduler_setup law
  have initial : SchedulerCapacity w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨signatures, slots, origin, c.initial_capacities law⟩
  have submitted := c.run.remaining.submit_call
  rw [c.code_length] at submitted
  have certified := compiler_submit_executable_source_capacities ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code c.run.remaining.config c.raw c.functions c.entryBounds (c.valid.environment_within_limits c.matched.2)
    c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.capacities_of_submission law certified.functions

/-- Public compilation of a module for WebAssembly Core 2.0 produces
source-ordered frame-capacity certificates for the exact canonical module syntax. -/
theorem compile_executable_capacities {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    ∃ raw, Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) raw bytes.val ∧
      Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw) ∧
      Module.Elaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (Module.Elaboration.moduleOf raw) ∧ Module.Elaboration.Restrictions raw ∧
      Module.Elaboration.AccessorTypes executable.module.env raw ∧
      ModuleCapacities executable (sourceFunctions raw) := by
  obtain ⟨w⟩ := compile_accepted ops bytes limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.executable_capacities law
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := Binary.Source.rawModuleInjective (WebAssembly.Binary.ModuleEncoding.unique encoded
    (Binary.Source.moduleEncoding c.encoded))
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    certificates⟩
end Itasca.Compiler

end

end

end
