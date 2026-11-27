import Itasca.Runtime.Compiler.Module.Definitions
import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Module.CollectionContracts
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Module.SourceAndSubmission
import Itasca.Stream.RetirementAndFraming
import Itasca.Runtime.Compiler.Local.Initializer.ModuleMappings
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Support.Translation
import Itasca.Runtime.Compiler.Local.Relations.Function.CapturedContext
import Itasca.Stream.SubmissionSound
import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Runtime.Compiler.Local.Capacity.ConditionalAndSimdAvailability
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryGrowth
import Itasca.Module.Code.Framing
import Itasca.Runtime.Compiler.Local.Capacity.ControlAvailability
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Runtime.Compiler.Local.Initializer.LowerContracts
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Source.ModuleSourceAndSubmission
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Body.Complete.Control

open WebAssembly

/-!
Proofs for Runtime / Compiler / Module.

This module collects DriverAndCodeRegions, PreparedFunctionDemand, SourceCertificatesAndInitializers, SourceMetadataAndSegments.
Each section documents its contracts and consumers.
-/

/-! ## DriverAndCodeRegions -/

section

open Itasca.Representation

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The concrete scheduler starts with empty tables, queues and counters. Its
construction is internal; public eligibility states only the required limits. -/
def initialScheduler (A : Type) (limits : runtime.compiler.CompileLimits) (codeStart : Usize) :
    runtime.compiler.CompileScheduler A :=
  { signatures := alloc.vec.Vec.new _, func_param_slots := alloc.vec.Vec.new _,
    completed := alloc.vec.Vec.new _, functions := alloc.vec.Vec.new _, tail := none,
    code_start := codeStart,
    budget := {marker := (), limits, instructions := 0#usize, branches := 0#usize, controls := 0#usize, locals := 0#usize, error := none} }


end Itasca.Compiler

/-!
# Driver And Code Regions

Driver environment frames and complete code regions connect module compilation to body-level certificates.
-/

/-! ## EnvironmentFrame -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.Computation

/-- Environment preparation does not alter queued workers, the source origin,
or the tail handoff. This statement follows from actual successful callbacks. -/
theorem compiler_environment_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (config : stream.StreamingConfig)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
      allocator before env = .ok (.Ok config, after)) : schedulerFrame after = schedulerFrame before := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.inv allocator before after env config accepted

end Itasca.Compiler

end

/-! ## CollectFunctions -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Moving a successful function into the dense executable vector preserves
its source slot and appends precisely that function. -/
@[step] theorem take_function_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (bound : index.val < pending.val.length) (capacity : functions.val.length < Usize.max) :
    runtime.compiler.take_function allocator budget pending index functions ⦃ out =>
      out.2.2.1.val.length = pending.val.length ∧
      (out.1 = .Ok () → ∃ function,
        pending.val[index.val]? = some (some function) ∧
        out.2.2.1.val = pending.val.set index.val none ∧
        out.2.2.2.val = functions.val ++ [function]) ⦄ := by
  exact runtime.compiler.take_function.total allocator law budget pending index functions bound capacity

@[step] theorem collect_functions_loop_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (original : List (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (result : core.result.Result Unit runtime.compiler.CompileError)
    (length : pending.val.length = original.length) (bound : index.val ≤ original.length)
    (invariant : result = .Ok () → CollectionPrefix original pending functions index.val) :
    runtime.compiler.collect_functions_loop allocator budget pending functions index result ⦃ out =>
      out.2.2.2 = .Ok () → original = out.2.2.1.val.map some ⦄ := by
  exact runtime.compiler.collect_functions_loop.total allocator law original budget pending functions index result length bound invariant

/-- Actual collection succeeds exactly in source order. The final pending
vector is internal; callers receive the dense vector with every original slot. -/
@[step] theorem collect_functions_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)) :
    runtime.compiler.collect_functions allocator budget pending ⦃ out =>
      ∀ functions, out.1 = .Ok functions → pending.val = functions.val.map some ⦄ := by
  exact runtime.compiler.collect_functions.total allocator law budget pending

end Itasca.Compiler

end

/-! ## SchedulerSubmission -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Metadata captured before any function compilation is fixed across all
actual entry calls in a submitted batch. -/
def schedulerStatic {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.signatures, scheduler.func_param_slots, scheduler.code_start)

theorem CompileEntryWitness.static {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch) :
    schedulerStatic after = schedulerStatic before := by rw [w.published]; rfl

theorem CompileEntries.static {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.StreamingBatch}
    (run : CompileEntries allocator before batch after finalBatch) :
    schedulerStatic after = schedulerStatic before := by
  induction run with
  | nil => rfl
  | next entry rest ih =>
    obtain ⟨w⟩ := compile_entry_accepted _ _ _ _ _ entry
    exact ih.trans w.static

end Itasca.Compiler

end

/-! ## SchedulerSafety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- The eager scheduler's raw metadata and queue bounds at the next submitted
function index. No successful final module or semantic code certificate is used. -/
structure SchedulerReady {A : Type} (env : metadata.Env) (cursor : Nat)
    (scheduler : CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ty => signatureSlots ty.params.val)
  functions : scheduler.functions.val.length = env.func_type_indices.val.length
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  queue : scheduler.completed.val.length ≤ cursor
  cursorBound : cursor ≤ env.func_type_indices.val.length

/-- Initial scheduler fields before the environment callback. -/
structure SchedulerInitial {A : Type} (scheduler : CompileScheduler A) : Prop where
  signatures : scheduler.signatures.val = []
  functionSlots : scheduler.func_param_slots.val = []
  functions : scheduler.functions.val = []
  queue : scheduler.completed.val = []
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val

@[step] theorem compiler_environment_safety {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : CompileScheduler A)
    (env : metadata.Env) (initial : SchedulerInitial scheduler) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ out =>
      ∀ config, out.1 = .Ok config → SchedulerReady env 0 out.2 ⦄ := by
  obtain ⟨⟨status,after⟩,run,post⟩ := WP.spec_imp_exists
    (compiler_environment_ready_sequence ops law scheduler env initial.signatures initial.functionSlots initial.functions)
  rw [run]
  apply (WP.spec_ok _).mpr
  intro config accepted
  dsimp only at accepted
  obtain ⟨signatures,slots,functions⟩ := post config accepted
  have unchanged := compiler_environment_frame ops scheduler after env config (by simpa only [accepted] using run)
  have fields : after.completed = scheduler.completed ∧ after.tail = scheduler.tail ∧ after.code_start = scheduler.code_start := by
    simpa [schedulerFrame] using unchanged
  refine ⟨signatures,slots,?_,?_,?_,Nat.zero_le _⟩
  · simp [functions]
  · simpa [fields.2.2] using initial.origin
  · simp [fields.1,initial.queue]

@[step] theorem compiler_poll_safety {A : Type} (ops : runtime.platform.Alloc A)
    (env : metadata.Env) (cursor : Nat) (scheduler : CompileScheduler A)
    (ready : SchedulerReady env cursor scheduler) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch ops scheduler ⦃ out =>
      ∀ batch, out.1 = .Ok batch → SchedulerReady env cursor out.2 ⦄ := by
  rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch.eq]
  simp only [alloc.vec.Vec.pop,bind_ok]
  cases present : scheduler.completed.val.getLast? with
  | none => simp [core.option.Option.ok_or]
  | some batch =>
    simp [core.option.Option.ok_or]
    exact ⟨ready.signatures,ready.functionSlots,ready.functions,ready.origin,
      (by dsimp only; rw [alloc.vec.Vec.from_val]; simp only [List.length_dropLast]; have := ready.queue; omega),ready.cursorBound⟩

end Itasca.Compiler

end

/-! ## CompileEntryTotal -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Dispatch, compiler construction, final bytecode checking, and indexed
publication return normally. The remaining body obligation names only the
fresh compiler reached by this actual issued entry. -/
theorem compiler_entry_total_of_validation {A : Type} (ops : runtime.platform.Alloc A)
    (before : CompileScheduler A) (issued : Stream.Batch.Issued) (batch : stream.StreamingBatch)
    (bounded : issued.Bounded) (reachable : Stream.Batch.Reachable issued batch)
    (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (validation : ∀ (entry : stream.StreamingEntry) (dispatched : stream.StreamingBatch)
      (batchStart : Usize) (initial : FunctionCompiler A),
      stream.StreamingBatch.next_entry batch = .ok (.Ok entry,dispatched) →
      (before.code_start + dispatched.code_offset : Result Usize) = .ok batchStart →
      FunctionCompiler.new ops (alloc.vec.Vec.deref before.signatures)
        (alloc.vec.Vec.deref before.func_param_slots) {before.budget with marker := ()} batchStart = .ok initial →
      stream.StreamingBatch.validate_func (FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        dispatched entry.index initial ⦃ _ => True ⦄) :
    runtime.compiler.CompileScheduler.compile_entry ops before batch ⦃ _ => True ⦄  := by
  exact runtime.compiler.CompileScheduler.compile_entry.total ops before issued batch
    bounded reachable origin validation

end Itasca.Compiler

end

/-! ## CompileAssembly -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.Computation

def uninitializedModule (env : metadata.Env) (tail : metadata.Tail)
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) : runtime.compiler.ExecutableModule :=
  { module := {env, tail}, functions, global_initializers := alloc.vec.Vec.new _,
    element_initializers := alloc.vec.Vec.new _, element_offsets := alloc.vec.Vec.new _,
    data_offsets := alloc.vec.Vec.new _, initialization := 0#usize }

/-- A successful public compiler run retains the actual canonical streaming
validation, source-ordered function collection, and initializer-lowering calls. -/
structure CompileWitness {A : Type} (allocator : runtime.platform.Alloc A)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (executable : runtime.compiler.ExecutableModule) where
  codeStart : Usize
  codeEnd : Usize
  initialEnv : metadata.Env
  env : metadata.Env
  scheduler : runtime.compiler.CompileScheduler A
  tail : metadata.Tail
  functions : alloc.vec.Vec runtime.bytecode.CompiledFunction
  pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)
  collectedBudget : runtime.compiler.Budget A
  finalBudget : runtime.compiler.Budget A
  region : runtime.compiler.code_region bytes = .ok (codeStart, codeEnd)
  initialized : metadata.Env.new = .ok initialEnv
  validated : stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := codeStart, code_end := codeEnd}
    (initialScheduler A limits codeStart) initialEnv = .ok (.Ok (), scheduler, env)
  tailReady : scheduler.tail = some tail
  collected : runtime.compiler.collect_functions allocator scheduler.budget scheduler.functions =
    .ok (.Ok functions, collectedBudget, pending)
  lowered : runtime.compiler.initialize.lower allocator (uninitializedModule env tail functions)
    collectedBudget = .ok (.Ok (), executable, finalBudget)

theorem compile_accepted {A : Type} (allocator : runtime.platform.Alloc A)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok executable)) :
    Nonempty (CompileWitness allocator bytes limits executable) := by
  unfold runtime.compiler.compile_with at accepted
  dsimp only at accepted
  split at accepted
  · simp at accepted
  · obtain ⟨⟨codeStart, codeEnd⟩, region, rest⟩ := bind_ok_inv _ _ _ accepted
    obtain ⟨initialEnv, initialized, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨⟨result, scheduler, env⟩, validated, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => cases choice : scheduler.budget.error <;> simp [choice] at rest
    | Ok acceptedUnit =>
      cases acceptedUnit
      simp only [uncurry_apply_pair] at rest
      cases tailReady : scheduler.tail with
      | none => simp [tailReady, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | some tail =>
        simp only [tailReady, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨result, collectedBudget, pending⟩, collected, rest⟩ := bind_ok_inv _ _ _ rest
        cases result with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok functions =>
          simp only [uncurry_apply_pair, bind_ok] at rest
          obtain ⟨⟨result, output, finalBudget⟩, lowered, rest⟩ := bind_ok_inv _ _ _ rest
          cases result with
          | Err error => cases choice : finalBudget.error <;> simp [choice] at rest
          | Ok acceptedUnit =>
            cases acceptedUnit
            simp at rest
            subst output
            exact ⟨⟨codeStart, codeEnd, initialEnv, env, scheduler, tail, functions, pending,
              collectedBudget, finalBudget, region, initialized, validated, tailReady, collected, lowered⟩⟩

section
open runtime.compiler

theorem _root_.Itasca.runtime.compiler.compile_with.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : CompileLimits)
    (streaming : ∀ (codeStart codeEnd : Usize) (storage : metadata.Env),
      codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length →
      stream.validate_streaming CompileSource.Insts.ItascaStreamStreamingSource
        (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
        {bytes,code_start := codeStart,code_end := codeEnd}
        (initialScheduler A limits codeStart) storage ⦃ out =>
          True ⦄)
    (lowering : ∀ (codeStart codeEnd : Usize) (storage env : metadata.Env)
      (scheduler : CompileScheduler A) (tail : metadata.Tail)
      (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
      (budget : Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)),
      codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length →
      stream.validate_streaming CompileSource.Insts.ItascaStreamStreamingSource
        (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
        {bytes,code_start := codeStart,code_end := codeEnd}
        (initialScheduler A limits codeStart) storage = .ok (.Ok (), scheduler, env) →
      scheduler.tail = some tail →
      collect_functions ops scheduler.budget scheduler.functions = .ok (.Ok functions, budget, pending) →
      initialize.lower ops (uninitializedModule env tail functions) budget ⦃ _ => True ⦄) :
    runtime.compiler.compile_with ops bytes limits ⦃ _ => True ⦄ := by
  unfold runtime.compiler.compile_with
  dsimp only
  split
  · simp
  · obtain ⟨⟨codeStart,codeEnd⟩,region,bounds⟩ := WP.spec_imp_exists (code_region_spec bytes)
    obtain ⟨storage,initialized,_⟩ := WP.spec_imp_exists metadata.Env.new.spec
    simp only [region,initialized,bind_ok,uncurry_apply_pair]
    obtain ⟨⟨status,scheduler,env⟩,validated,ready⟩ := WP.spec_imp_exists (streaming codeStart codeEnd storage bounds)
    simp only [initialScheduler] at validated
    simp only [validated]
    simp only [bind_ok,uncurry_apply_pair]
    cases status with
    | Err error => cases scheduler.budget.error <;> simp
    | Ok acceptedUnit =>
      cases acceptedUnit
      cases tailReady : scheduler.tail with
      | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some tail =>
        simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        obtain ⟨⟨collected,budget,pending⟩,collect,order⟩ := WP.spec_imp_exists
          (collect_functions_spec ops law scheduler.budget scheduler.functions)
        rw [collect]
        simp only [bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
        cases collected with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok functions =>
          obtain ⟨⟨result,executable,finalBudget⟩,lowered,_⟩ := WP.spec_imp_exists
            (lowering codeStart codeEnd storage env scheduler tail functions budget pending bounds
              (by simpa only [initialScheduler] using validated) tailReady collect)
          simp only [bind_ok]
          simp only [uninitializedModule] at lowered
          rw [lowered]
          cases result <;> cases choice : finalBudget.error <;> simp [choice]

/-- A successful sequence of actual compiler stages publishes its executable
when the independent module-byte limit permits entry. -/
theorem _root_.Itasca.runtime.compiler.compile_with.available {A : Type}
    {ops : runtime.platform.Alloc A} {bytes : Slice U8} {limits : CompileLimits}
    {executable : ExecutableModule} (fits : bytes.length ≤ limits.max_module_bytes.val)
    (w : CompileWitness ops bytes limits executable) :
    compile_with ops bytes limits = .ok (.Ok executable) := by
  have size : ¬ Slice.len bytes > limits.max_module_bytes := by scalar_tac
  unfold runtime.compiler.compile_with
  simp only [if_neg size, w.region, bind_ok, uncurry_apply_pair, w.initialized]
  have validated := w.validated
  simp only [initialScheduler] at validated
  simp only [validated, bind_ok, uncurry_apply_pair, w.tailReady, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, w.collected]
  have lowered := w.lowered
  simp only [uninitializedModule] at lowered
  rw [lowered]
  simp only [bind_ok]
  rfl

end

/-- The actual collection witness fixes the exact order of the defined code. -/
theorem CompileWitness.function_order {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) : w.scheduler.functions.val = w.functions.val.map some := by
  have collected := collect_functions_spec allocator law w.scheduler.budget w.scheduler.functions
  rw [w.collected, WP.spec_ok] at collected
  exact collected w.functions rfl

/-- Successful initializer lowering preserves the validated module and all
defined functions, and establishes the concrete read-only initializer maps. -/
theorem CompileWitness.initializers {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    executable.module = ⟨w.env, w.tail⟩ ∧
      executable.functions.val.take w.functions.length = w.functions.val ∧ InitializerMappings executable := by
  exact initializer_lower allocator law (uninitializedModule w.env w.tail w.functions) executable
    w.collectedBudget w.finalBudget (by rfl) (by rfl) (by rfl) (by rfl) w.lowered

end Itasca.Compiler

end

/-! ## CompilerDrain -/

section

/-!
Compiler worker provenance and drain preservation. SchedulerTracks records issued worker origins through queue operations and final draining.
-/

/-! ## Compiler Provenance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca

/-- Every completed worker comes from one issued batch in a history with unique
batch identifiers. The history is an internal invariant of the actual driver. -/
structure SchedulerTracks {A : Type} (_id : U64) (history : List Stream.Batch.Issued)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  unique : ∀ left ∈ history, ∀ right ∈ history, left.batch_id = right.batch_id → left = right
  workers : ∀ batch ∈ scheduler.completed.val, ∃ issued ∈ history, Stream.Batch.Reachable issued batch

theorem SchedulerTracks.queue {A : Type} {id history} {before after : runtime.compiler.CompileScheduler A}
    (tracked : SchedulerTracks id history before) (same : after.completed = before.completed) :
    SchedulerTracks id history after := by
  exact ⟨tracked.unique, by simpa only [same] using tracked.workers⟩

/-- The concrete compiler satisfies the canonical streaming scheduler's
provenance contract. Allocation decisions remain unrestricted. -/
theorem compiler_provenance {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) :
    Stream.Scheduler.Provenance
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
      SchedulerTracks := by
  constructor
  · intro id history before chunk after accepted tracked
    have same : before = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_metadataModuleVisitorInst.eq,
        runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.project_on_custom_section.eq,
        runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section.eq,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked
  · intro id history before region after tracked accepted
    have same : before = after := Result.ok_injective accepted
    subst after
    exact tracked
  · intro id history before env config after tracked accepted
    exact tracked.queue (congrArg Prod.fst (compiler_environment_frame allocator before after env config accepted))
  · intro id history issued before after tracked moduleId bounded envBounds fresh accepted
    obtain ⟨middle, worker, run, queue, _⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
    constructor
    · intro left hl right hr equal
      rcases List.mem_append.mp hl with hl | hl <;> rcases List.mem_append.mp hr with hr | hr
      · exact tracked.unique left hl right hr equal
      · have rightEq := List.mem_singleton.mp hr
        subst right
        exact (fresh left hl equal).elim
      · have leftEq := List.mem_singleton.mp hl
        subst left
        exact (fresh right hr equal.symm).elim
      · exact (List.mem_singleton.mp hl).trans (List.mem_singleton.mp hr).symm
    · intro batch member
      rw [queue] at member
      rcases List.mem_append.mp member with old | new
      · obtain ⟨origin, member, reachable⟩ := tracked.workers batch old
        exact ⟨origin, List.mem_append_left _ member, reachable⟩
      · have same := List.mem_singleton.mp new
        subst batch
        exact ⟨issued, by simp, run.reachable .seed⟩
  · intro id history before batch after tracked accepted
    obtain ⟨queue, same⟩ := compiler_poll_accepted allocator before after batch accepted
    constructor
    · refine ⟨tracked.unique, ?_⟩
      intro worker member
      exact tracked.workers worker (by rw [queue]; exact List.mem_append_left _ member)
    · intro issued member moduleId batchId
      obtain ⟨origin, originMember, reachable⟩ := tracked.workers batch (by rw [queue]; simp)
      have identity := reachable.validation.1
      have sameOrigin := tracked.unique origin originMember issued member (identity.2.1.symm.trans batchId.symm)
      subst origin
      exact reachable
  · intro id history before after tracked accepted
    have same : before = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_code_end.eq,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end.eq,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked
  · intro id history before tail after tracked accepted
    have same : {before with tail := some tail} = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked.queue rfl
end Itasca.Compiler

end

/-! ## Compiler Drain -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.Computation

/-- The final drain only removes completed workers. All captured code and the
validated tail remain exactly as delivered before retirement. -/
theorem compiler_drain_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (id : U64) (before after : runtime.compiler.CompileScheduler A)
    (pending remaining : alloc.vec.Vec Usize)
    (accepted : stream.retire_all_code_batches
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
      id before pending = .ok (.Ok (), after, remaining)) :
    after = {before with completed := after.completed} := by
  generalize measure : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing before pending with
  | h n ih =>
    unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop at accepted
    rw [loop] at accepted
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok] at accepted
    by_cases empty : pending.val = []
    · simp [empty] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      rfl
    · have nonempty : pending.val.isEmpty = false := by simpa using empty
      simp only [nonempty, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc] at accepted
      obtain ⟨⟨result, middle, rest⟩, retired, tail⟩ := bind_ok_inv _ _ _ accepted
      cases result with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
      | Ok unit =>
        cases unit
        obtain ⟨batch, polled, _, _, perm⟩ := stream.retire_code_batch.accepted
          (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
          id before middle pending rest retired
        have length := perm.length_eq
        simp only [List.length_cons] at length
        have smaller : rest.val.length < n := by omega
        have tail' : stream.retire_all_code_batches
            (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
            id middle rest = .ok (.Ok (), after, remaining) := by
          simpa [stream.retire_all_code_batches, stream.retire_all_code_batches_loop,
            stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty,
            core.result.Result.Insts.CoreOpsTry.branch] using tail
        have afterEq := ih rest.val.length smaller middle rest tail' rfl
        have middleEq := (compiler_poll_accepted allocator before middle batch polled).2
        rw [afterEq, middleEq]
end Itasca.Compiler

end

end

/-! ## CompileSource -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca

/-- The concrete source scanner and compiler scheduler discharge all embedding
premises of the existing validator's accepted-module theorem. -/
theorem CompileWitness.source_validated {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    Module.Sound.Validated bytes executable.module ∧ bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have bounded : SourceBounds source := bounds
  have available := source_available source bounded
  obtain ⟨environment, _, he⟩ := available.environment_read
  obtain ⟨tail, _, ht⟩ := available.tail_read
  obtain ⟨len, _, hl⟩ := available.code_len_read
  obtain ⟨code, _, hc⟩ := available.code_read 0#usize len (by scalar_tac) (by omega)
  have hc' : code.val = sourceCode source := by
    simpa [List.slice, hl] using hc
  have coherent : Stream.Source.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource source
      environment.val code.val tail.val := by
    rw [he, hc', ht]
    exact source_coherent source bounded
  have recombine : bytes.val = environment.val ++ code.val ++ tail.val := by
    rw [he, hc', ht]
    exact (source_recombine source bounded).symm
  have initial : SchedulerTracks 0#u64 [] (initialScheduler A limits w.codeStart) := by
    constructor
    · simp
    · simp [initialScheduler]
  obtain ⟨run, validated, size⟩ := stream.validate_streaming.sound_core
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    SchedulerTracks (compiler_provenance allocator law) 0#u64 source
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env bytes environment code tail
    coherent recombine initial w.validated
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  refine ⟨?_, size⟩
  rw [(w.initializers law).1]
  simpa only [sameTail] using validated

/-- Every accepted public compilation validates exactly its input bytes. This theorem makes no compiler-certificate premise. -/
theorem compile_source_validated {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok executable)) :
    Module.Sound.Validated bytes executable.module ∧
      bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  obtain ⟨w⟩ := compile_accepted allocator bytes limits executable accepted
  obtain ⟨validated, size⟩ := w.source_validated law
  exact ⟨validated, size⟩
end Itasca.Compiler

end

/-! ## CodeRegionComplete -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Binary
set_option maxRecDepth 4096

private def compilerScan (data : Slice U8) (pos : Usize) :=
  runtime.compiler.code_region_loop data pos false (Slice.len data) (Slice.len data)

private theorem compiler_found (data : Slice U8) (pos first last : Usize) :
    runtime.compiler.code_region_loop data pos true first last = .ok (first,last) := by
  exact runtime.compiler.code_region_loop.done data pos true first last first last
    (runtime.compiler.code_region_loop.body.stopped data pos true first last (Or.inr rfl))

private theorem compiler_split_body_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (allowed : id.val ≤ 10 ∨ id.val = 12) :
    runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) =
      .ok (if id = 10#u8 then .cont (last,true,pos,last)
        else .cont (last,false,Slice.len data,Slice.len data)) := by
  have noStop : ¬ (id > 10#u8 ∧ id ≠ 12#u8) := by
    intro stopped
    rcases allowed with lower | count
    · scalar_tac
    · exact stopped.2 (UScalar.eq_of_val_eq count)
  simpa only [if_neg noStop] using
    runtime.compiler.code_region_loop.body.available data pos first last id h

private theorem compiler_split_loop_eof (data : Slice U8) :
    compilerScan data (Slice.len data) = .ok (Slice.len data,Slice.len data) := by
  change runtime.compiler.code_region_loop data (Slice.len data) false (Slice.len data) (Slice.len data) = _
  exact runtime.compiler.code_region_loop.done data (Slice.len data) false (Slice.len data) (Slice.len data)
    (Slice.len data) (Slice.len data)
    (runtime.compiler.code_region_loop.body.stopped data (Slice.len data) false (Slice.len data) (Slice.len data)
      (Or.inl (by simpa only [Slice.len_val] using Nat.le_refl data.length)))

private theorem compiler_split_skip_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (allowed : id.val < 10 ∨ id.val = 12) :
    compilerScan data pos = compilerScan data last := by
  have body := compiler_split_body_section data pos first last id h (by omega)
  have notCode : id ≠ 10#u8 := by scalar_tac
  simp only [if_neg notCode] at body
  exact runtime.compiler.code_region_loop.step data pos false (Slice.len data) (Slice.len data)
    last false (Slice.len data) (Slice.len data) body

private theorem compiler_split_code_section (data : Slice U8) (pos first last : Usize)
    (h : SectionHeader data pos 10#u8 first last) : compilerScan data pos = .ok (pos,last) := by
  have body := compiler_split_body_section data pos first last 10#u8 h (by decide)
  simp only [↓reduceIte] at body
  change runtime.compiler.code_region_loop data pos false (Slice.len data) (Slice.len data) = _
  rw [runtime.compiler.code_region_loop.step data pos false (Slice.len data) (Slice.len data)
    last true pos last body]
  exact compiler_found data last pos last

private theorem compiler_split_after_code (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (high : 10 < id.val) (notCount : id.val ≠ 12) :
    compilerScan data pos = .ok (pos,pos) := by
  have above : id > 10#u8 := by scalar_tac
  have different : id ≠ 12#u8 := by
    intro same
    have value := congrArg UScalar.val same
    scalar_tac
  have body := runtime.compiler.code_region_loop.body.available data pos first last id h
  simp only [if_pos (And.intro above different)] at body
  change runtime.compiler.code_region_loop data pos false (Slice.len data) (Slice.len data) = _
  rw [runtime.compiler.code_region_loop.step data pos false (Slice.len data) (Slice.len data)
    pos true pos pos body]
  exact compiler_found data pos pos pos

private theorem compiler_split_skip_customs {data : Slice U8} {bytes : List U8}
    (h : CustomsEncoding bytes) {pos next : Usize} (hb : Body.Scalar.BytesAt data pos bytes next) :
    compilerScan data pos =
      compilerScan data next := by
  induction h generalizing pos with
  | nil => rw [hb.empty]
  | cons hc _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨nm, payload, encodedName, _, hs⟩ := hc
    obtain ⟨content, hh, _⟩ := (show At
      (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = encodedName ++ payload))
      data pos () middle from ⟨_, hs, hfirst⟩).section_split
    rw [compiler_split_skip_section data pos content middle 0#u8 hh (by decide)]
    exact ih hrest

private theorem compiler_split_skip_chain {data : Slice U8} {raw n bytes}
    (h : Module.Environment.Chain raw n bytes) {pos next : Usize}
    (hb : Body.Scalar.BytesAt data pos bytes next) :
    compilerScan data pos =
      compilerScan data next := by
  induction h generalizing pos with
  | done hc => exact compiler_split_skip_customs hc hb
  | @step n id first rest hn hid hslot _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨customs, sec, hc, hs, he⟩ := hslot
    rw [he] at hfirst
    obtain ⟨afterCustoms, hcustoms, hsection⟩ := hfirst.split
    rw [compiler_split_skip_customs hc hcustoms]
    rcases hs with ⟨_, rfl⟩ | hs
    · rw [← hsection.empty]
      exact ih hrest
    · obtain ⟨content, hh, _⟩ := (show
        At (SectionEncoding id (fun u bs => Module.Environment.Payload raw (sectionRank id).val u bs)) data afterCustoms () middle
        from ⟨_, hs, hsection⟩).section_split
      rw [compiler_split_skip_section data afterCustoms content middle id hh (by
        have hrange := section_rank_prefix (id := id) (by omega) (by omega)
        omega)]
      exact ih hrest

theorem compiler_split_skip_prefix {data : Slice U8} {decls next}
    (h : At (fun ds bs => Module.Environment.PrefixEncoding ds bs) data 0#usize decls next) :
    compilerScan data 8#usize =
      compilerScan data next := by
  obtain ⟨bytes, hp, hb⟩ := h
  obtain ⟨suffix, hc, he⟩ := hp.chain [] []
  rw [he] at hb
  obtain ⟨middle, hmagic, hchain⟩ := hb.split
  have hm : middle = 8#usize := by
    apply UScalar.eq_of_val_eq
    simpa [magicVersion] using hmagic.length
  subst middle
  exact compiler_split_skip_chain hc hchain

/-- On an independently valid normalized layout, the splitter returns the environment, code and
tail boundaries used by component completeness. -/
theorem compiler_code_region_complete_layout {data : Slice U8} {raw decls codePos tailPos}
    (h : Module.Layout data raw decls codePos tailPos) :
    runtime.compiler.code_region data = .ok (codePos, tailPos) := by
  change compilerScan data 8#usize = _
  rw [compiler_split_skip_prefix h.environment]
  rcases h.code with hc | ⟨_, hsame, hstop⟩
  · obtain ⟨first, hh, _⟩ := hc.section_split
    exact compiler_split_code_section data codePos first tailPos hh
  · subst tailPos
    rcases hstop with heof | ⟨id, first, last, hh, hne⟩
    · have he : codePos = Slice.len data := by apply UScalar.eq_of_val_eq; simpa using heof
      rw [he]
      exact compiler_split_loop_eof data
    · rcases h.stop with heof | ⟨id', first', last', hh', hge⟩
      · have hs := hh.span
        have he := congrArg UScalar.val heof
        simp only [Slice.len_val] at he
        omega
      · have he : id = id' ∧ first = first' ∧ last = last' := by
          have hread := (metadata.read_section_header.complete data codePos id first last hh).symm.trans
            (metadata.read_section_header.complete data codePos id' first' last' hh')
          simpa using hread
        have hid : id = 11#u8 := by
          rcases hge with hc | hd
          · exact False.elim (hne (he.1.trans hc))
          · exact he.1.trans hd
        exact compiler_split_after_code data codePos first last id hh
          (by simp [hid]) (by simp [hid])

/-- On independently encoded modules, both concrete scanners select the same
canonical byte coordinates despite their different loop control states. -/
theorem compiler_code_region_eq_stream (data : Slice U8) (raw : Binary.Module)
    (encoded : ModuleEncodingWithinLimits raw data.val) :
    runtime.compiler.code_region data = Itasca.stream.find_code_region data := by
  obtain ⟨decls,codeStart,codeEnd,layout⟩ := Module.normalize data raw encoded
  rw [compiler_code_region_complete_layout layout,Itasca.stream.find_code_region.complete_layout layout]

end Itasca.Compiler

end

end

/-! ## PreparedFunctionDemand -/

section

/-!
Proofs for Runtime / Compiler / Module.

This module collects SegmentSource, PreparedFunctionDemand.
Each section documents its contracts and consumers.
-/

/-! ## SegmentSource -/

section

open Itasca.Representation

/-! ## CompileSemantic -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful canonical environment and tail validation expose their checked
semantic facts before compiler assembly. No binary typing inversion or compiler
correctness premise is needed to recover these actual validator postconditions. -/
theorem CompileWitness.semantic_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable) :
    Module.Environment.Valid w.env ∧
      (∀ segment ∈ w.tail.data.val, Module.Data.Valid w.env segment) := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have decoded := metadata.validate_env_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.environment run.region w.env run.environmentLength run.decoded run.decode_environment
  have semantic := metadata.validate_env.semantic_spec run.environment
  rw [decoded, WP.spec_ok] at semantic
  obtain ⟨decls, represented, valid, _, _, before, sourcePrefix, span⟩ := semantic
  have tailDecoded := metadata.validate_tail_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.remaining.tailBytes 0#usize w.env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have tailSemantic := metadata.validate_tail.spec run.remaining.tailBytes 0#usize w.env (by simp)
  rw [tailDecoded, WP.spec_ok] at tailSemantic
  obtain ⟨_, segments, _⟩ := tailSemantic
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  exact ⟨valid, by simpa only [sameTail] using segments⟩

/-- Canonical validity belongs to the exact metadata retained in the accepted
executable, including the data tail actually delivered to the compiler. -/
theorem CompileWitness.semantic {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    Module.Environment.Valid executable.module.env ∧
      (∀ segment ∈ executable.module.tail.data.val, Module.Data.Valid executable.module.env segment) := by
  rw [(w.initializers law).1]
  exact w.semantic_input

/-- Actual successful public compilation constructs the retained segment program
certificate, using the canonical validator's checked active-offset typing. -/
theorem CompileWitness.segment_program {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∃ function, executable.functions.val[executable.initialization.val]? = some function ∧
      SegmentProgram executable function := by
  obtain ⟨valid, datas⟩ := w.semantic_input
  have elements : ∀ segment ∈ w.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Module.Constants.Valid w.env offset .I32 := by
    intro segment member table offset mode
    have typed := (valid.elements segment member).1
    obtain ⟨bound, tableType, offsetValid⟩ := (show ∃ h : table.val < w.env.table_types.val.length,
      w.env.table_types.val[table.val].elem = segment.elem ∧ Module.Constants.Valid w.env offset .I32 from by simpa [mode] using typed)
    exact offsetValid
  have dataOffsets : ∀ segment ∈ w.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Module.Constants.Valid w.env offset .I32 := by
    intro segment member memory offset mode
    have typed := datas segment member
    exact (show memory.val < w.env.mem_types.val.length ∧ Module.Constants.Valid w.env offset .I32 from
      by simpa [Module.Data.Valid, mode] using typed).2
  have result := initializer_lower_segments allocator law _ _ _ _ rfl rfl rfl rfl elements dataOffsets w.lowered
  exact result.2.2.2

end Itasca.Compiler

end

/-! ## SegmentSource -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Accepted source bytes supply the binary framing and metadata coherence
needed by the retained initializer's program-counter bound. -/
theorem segment_validated_pc_bound {module function bytes}
    (certificate : SegmentProgram module function)
    (validated : Itasca.Module.Sound.Validated bytes module.module)
    (bounded : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    function.code.length < U32.max := by
  obtain ⟨raw, encoded, _, matched, _⟩  := validated
  have elements := congrArg (fun raw : Itasca.Binary.Module => raw.elements.length) matched.1
  have datas := congrArg (fun raw : Itasca.Binary.Module => raw.data.length) matched.1
  apply certificate.pc_bound encoded (by simpa [Binary.Source.bytes] using bounded)
  · simpa [Binary.Source.rawModule, Itasca.Module.Elaboration.fromEnv] using elements.symm
  · simpa [Binary.Source.rawModule, Itasca.Module.Elaboration.fromEnv] using datas.symm

/-- No extra runtime limit premise is required for the initializer PC: the
successful public compiler already checked the fixed module-byte cap. -/
theorem segment_compile_pc_bound {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (module : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module))
    (function : runtime.bytecode.CompiledFunction) (certificate : SegmentProgram module function) :
    function.code.length < U32.max := by
  obtain ⟨validated, bounded⟩ := compile_source_validated allocator law bytes limits module accepted
  exact segment_validated_pc_bound certificate validated bounded

end Itasca.Compiler

end

end

/-! ## PreparedFunctionDemand -/

section

open Itasca.Representation

/-! ## CollectionAvailable -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- The actual dense collection succeeds in source order and preserves all
budget counters. Population is established by compilation's source-slot prefix. -/
theorem collect_functions_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (reserve : pending.length ≤ bound)
    (populated : ∀ index, index < pending.length → ∃ function, pending.val[index]? = some (some function)) :
    runtime.compiler.collect_functions ops budget pending ⦃ out => out.2.1 = budget ∧
      ∃ functions, out.1 = .Ok functions ∧ pending.val = functions.val.map some ⦄ := by
  exact runtime.compiler.collect_functions.available ops law bound allocation budget pending reserve populated

end Itasca.Compiler

end

/-! ## PreparedEntryReplay -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Exact prepared source bytes replay the actual entry parser around its two
visitor-bearing calls. This requires only those reached calls, rather than a
visitor that accepts arbitrary contexts or instruction traces. -/
theorem prepared_entry_replay {V : Type} (visitor : code.OpVisitor V)
    {data env index start} (w : CodeEntry.Prepared data env index start)
    (before started after : V)
    (begun : visitor.on_function_start before w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started))
    (body : code.validate_body_with visitor w.body env w.ctx w.typeIdx started = .ok (.Ok (),after)) :
    metadata.validate_code_entry_with visitor data start env index before
      ⦃ result => result = (.Ok w.finish,after) ⦄ := by
  have read := reader.read_u32_leb.complete data start w.size w.content w.header
  obtain ⟨declared,decoded,declaredValues⟩ := metadata.decode_locals.complete data w.content w.groups w.bodyStart
    w.locals_bytes w.locals_bound
  have indexBound : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by
    have bound := w.index_lt
    scalar_tac
  unfold metadata.validate_code_entry_with
  simp [indexBound,read,core.result.Result.Insts.CoreOpsTry.branch]
  step
  obtain ⟨reply,haveBytes,haveBytesPost⟩ := WP.spec_imp_exists
    (metadata.have_bytes.spec data w.content n (by have bound := w.header.span; omega))
  have enough : reply = .Ok () := haveBytesPost.1.mpr (by have bound := w.body_bytes.bound; have extent := w.extent; scalar_tac)
  rw [enough] at haveBytes
  simp [haveBytes]
  step
  have endEq : «end» = w.finish := UScalar.eq_of_val_eq (by have extent := w.extent; scalar_tac)
  simp [decoded]
  have span := w.body_bytes.length
  have bodyStartBound : ¬ «end».val < w.bodyStart.val := by rw [endEq]; omega
  simp only [bodyStartBound,↓reduceIte]
  step
  have typeEq : type_idx = w.typeIdx := by simpa only [w.index_type] using type_idx_post
  step
  have typeBound : ¬ env.types.val.length ≤ t.val := by have bound := w.type_lt; rw [← typeEq] at bound; scalar_tac
  simp only [typeBound,↓reduceIte]
  step
  have functionEq : ft = w.ft := by
    simpa [t_post,typeEq,w.function_type] using ft_post
  have localRoom : ft.params.val.length+declared.val.length ≤ Usize.max := by
    rw [functionEq,declaredValues]
    have length := congrArg List.length w.context_locals
    simp only [List.length_append] at length
    have bound := w.ctx.locals.property
    omega
  obtain ⟨locals,build,localValues⟩ := WP.spec_imp_exists
    (metadata.build_func_locals.spec ft.params.deref declared.deref (by simpa [alloc.vec.Vec.deref] using localRoom))
  obtain ⟨results,copy,resultValues⟩ := WP.spec_imp_exists (metadata.copy_value_types.spec ft.results.deref)
  rw [build,copy]
  simp only [bind_ok]
  have localsEq : locals = w.ctx.locals := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.deref,functionEq,declaredValues,w.context_locals] using localValues)
  have resultsEq : results = w.ctx.results := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.deref,functionEq,w.context_results] using resultValues)
  have contextEq : (⟨locals,results⟩ : code.Context) = w.ctx := by rw [localsEq,resultsEq]
  rw [contextEq,typeEq,endEq,begun]
  simp only [bind_ok]
  step as ⟨actual,actualSpec⟩
  have bytes := Binary.slice_bytes (by have length := w.body_bytes.length; scalar_tac)
    w.body_bytes.bound actualSpec
  have bodyEq : actual = w.body := Slice.ext _ _ (by
    exact List.append_cancel_right (bytes.suffix.symm.trans w.body_bytes.suffix))
  rw [bodyEq,body]
  simp

end Itasca.Compiler

end

/-! ## PreparedFunctionDemand -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Conservative function demand measured solely in source body bytes,
expanded local declarations, and independently validated operand peak. -/
structure PreparedFunctionDemand {A : Type} (budget : runtime.compiler.Budget A)
    (ctx : code.Context) (length peak bound : Nat) : Prop where
  size : length ≤ limits.MAX_FUNCTION_BYTES.val
  instructions : budget.instructions.val+3*length ≤ budget.limits.max_instructions.val
  branches : budget.branches.val+length ≤ budget.limits.max_branch_table_entries.val
  controls : budget.controls.val+1+length ≤ budget.limits.max_controls.val
  locals : budget.locals.val+ctx.locals.val.length ≤ budget.limits.max_locals.val
  temporary : 3*length+3 ≤ bound
  localReserve : ctx.locals.val.length ≤ bound
  operands : peak ≤ bound
  slots : 2*ctx.locals.val.length+2*peak ≤ U32.max

/-- Fresh compiler construction turns source-only demand into every reserve
and arithmetic premise of the actual function-start callback. -/
theorem PreparedFunctionDemand.start {A : Type}
    {budget : runtime.compiler.Budget A} {ctx length peak bound}
    (demand : PreparedFunctionDemand budget ctx length peak bound)
    (ops : runtime.platform.Alloc A) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    FunctionStartDemand initial ctx bound := by
  simp only [runtime.compiler.FunctionCompiler.new.eq,Result.ok.injEq] at created
  subst initial
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  have localBound : ctx.locals.val.length ≤ Usize.max := by have slots := demand.slots; omega
  have one : 1 ≤ bound := by have temporary := demand.temporary; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact demand.locals
  · simpa [alloc.vec.Vec.new] using localBound
  · simpa [alloc.vec.Vec.new] using demand.localReserve
  · simpa [alloc.vec.Vec.new] using localBound
  · simpa [alloc.vec.Vec.new] using demand.localReserve
  · have slots := demand.slots
    simp only [show (0#u32).val = 0 from rfl,Nat.zero_add]
    omega
  · change budget.controls.val < budget.limits.max_controls.val
    have controls := demand.controls
    omega
  · simp [alloc.vec.Vec.new]; scalar_tac
  · simpa [alloc.vec.Vec.new] using one
  · simp [alloc.vec.Vec.new]; scalar_tac
  · simpa [alloc.vec.Vec.new] using one

/-- The actual start budget and local layout transfer the independent demand
into the complete body acceptance bound. -/
theorem PreparedFunctionDemand.body {A : Type}
    {budget : runtime.compiler.Budget A} {ctx length peak bound}
    (demand : PreparedFunctionDemand budget ctx length peak bound)
    (started : runtime.compiler.FunctionCompiler A) (usedLocals usedControls : Usize)
    (budgetFrame : started.budget = {budget with locals := usedLocals,controls := usedControls})
    (localsUsed : usedLocals.val = budget.locals.val+ctx.locals.val.length)
    (controlsUsed : usedControls.val = budget.controls.val+1)
    (layout : LocalLayout started) (localsMatch : started.function.locals = ctx.locals)
    (coordinate : started.function.body_start.val+length ≤ Usize.max) :
    BodyResourceRoom started length peak bound := by
  refine ⟨demand.size,?_,demand.temporary,demand.operands,?_,coordinate⟩
  · intro counter
    cases counter <;> simp only [ChargeCounter.used,ChargeCounter.limit,bodyResourceRate,budgetFrame,
      Nat.zero_mul,Nat.one_mul,localsUsed,controlsUsed]
    · exact demand.instructions
    · exact demand.branches
    · exact demand.controls
    · simpa only [Nat.add_zero] using demand.locals
  · have slotBound := slots_le_twice_length (compilerLocals started)
    have localLength : (compilerLocals started).length = ctx.locals.val.length := by
      simp [compilerLocals,localsMatch]
    rw [localLength] at slotBound
    rw [layout.slots]
    have room := demand.slots
    omega

end Itasca.Compiler

end

end

end

/-! ## SourceCertificatesAndInitializers -/

section

/-!
# Source Certificates And Initializers

Source certificates and initializer completion establish the final module compilation premises.
-/

/-! ## CompileSourceCertificate -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The canonical source syntax and exact code-region framing from an actual
public compilation. Keeping the accepted driver run fixes the configuration,
submission and tail states used by module certificate assembly. -/
structure CompileSourceCertificate {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness ops bytes limits executable) where
  environment : Slice U8
  code : Slice U8
  tail : Slice U8
  run : Stream.Run.Accepted runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.env
  coherent : Stream.Source.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} environment.val code.val tail.val
  recombined : bytes.val = environment.val ++ code.val ++ tail.val
  raw : Binary.Module
  encoded : Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) raw bytes.val
  matched : Module.Elaboration.Matches w.env run.remaining.tail raw
  valid : Module.Environment.Valid w.env
  entryBounds : CodeEntry.Bounds w.env
  functions : raw.functions = w.env.func_type_indices.val
  types : raw.types = w.env.types.val
  codeCount : raw.codes.length = w.env.func_type_indices.val.length
  header : Stream.Framing.HeaderAt code w.env run.remaining.entries
  entries : Binary.At (Binary.Rep (CodeEntry.CodeEncoding)) code run.remaining.entries raw.codes (Slice.len code)
  codeBound : code.length ≤ Itasca.limits.MAX_MODULE_BYTES.val
  moduleBound : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val

theorem CompileWitness.source_certificate {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness ops bytes limits executable)
    (law : Platform.AllocCorrect ops) : Nonempty (CompileSourceCertificate w) := by
  have bounds := code_region_spec bytes
  rw [w.region, WP.spec_ok] at bounds
  let source : runtime.compiler.CompileSource := {bytes, code_start := w.codeStart, code_end := w.codeEnd}
  have bounded : SourceBounds source := bounds
  have available := source_available source bounded
  obtain ⟨environment, _, he⟩ := available.environment_read
  obtain ⟨tail, _, ht⟩ := available.tail_read
  obtain ⟨len, _, hl⟩ := available.code_len_read
  obtain ⟨code, _, hc⟩ := available.code_read 0#usize len (by scalar_tac) (by omega)
  have hc' : code.val = sourceCode source := by simpa [List.slice, hl] using hc
  have coherent : Stream.Source.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource source
      environment.val code.val tail.val := by
    rw [he, hc', ht]
    exact source_coherent source bounded
  have recombine : bytes.val = environment.val ++ code.val ++ tail.val := by
    rw [he, hc', ht]
    exact (source_recombine source bounded).symm
  have initial : SchedulerTracks 0#u64 [] (initialScheduler A limits w.codeStart) := by
    constructor
    · simp
    · simp [initialScheduler]
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 source (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  obtain ⟨raw, encoded, matched, valid, entryBounds, functions, types, codeCount,
    header, entries, codeBound, moduleBound⟩ := stream_run_source
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    SchedulerTracks (compiler_provenance ops law) 0#u64 source
    (initialScheduler A limits w.codeStart) w.scheduler w.env bytes environment code tail coherent recombine initial run
  exact ⟨⟨environment, code, tail, run, coherent, recombine, raw, encoded, matched, valid,
    entryBounds, functions, types, codeCount, header, entries, codeBound, moduleBound⟩⟩
end Itasca.Compiler

end

/-! ## CompileStreamSource -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual successful streaming phase supplies source encoding and exact
module metadata before initializer lowering is attempted. -/
theorem compiler_stream_source {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (codeStart codeEnd : Usize)
    (storage env : metadata.Env) (scheduler : runtime.compiler.CompileScheduler A)
    (tail : metadata.Tail)
    (bounds : codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length)
    (tailReady : scheduler.tail = some tail)
    (accepted : stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
      {bytes,code_start := codeStart,code_end := codeEnd}
      (initialScheduler A limits codeStart) storage = .ok (.Ok (),scheduler,env)) :
    ∃ raw, Binary.ModuleEncodingWith (CodeEntry.CodeEncoding) raw bytes.val ∧
      Module.Elaboration.Matches env tail raw ∧ raw.functions = env.func_type_indices.val ∧
      bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  let source : runtime.compiler.CompileSource := {bytes,code_start := codeStart,code_end := codeEnd}
  have bounded : SourceBounds source := bounds
  have available := source_available source bounded
  obtain ⟨environment,_,he⟩ := available.environment_read
  obtain ⟨tailBytes,_,ht⟩ := available.tail_read
  obtain ⟨len,_,hl⟩ := available.code_len_read
  obtain ⟨code,_,hc⟩ := available.code_read 0#usize len (by scalar_tac) (by omega)
  have hc' : code.val = sourceCode source := by simpa [List.slice,hl] using hc
  have coherent : Stream.Source.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
      source environment.val code.val tailBytes.val := by
    rw [he,hc',ht]
    exact source_coherent source bounded
  have recombine : bytes.val = environment.val ++ code.val ++ tailBytes.val := by
    rw [he,hc',ht]
    exact (source_recombine source bounded).symm
  have initial : SchedulerTracks 0#u64 [] (initialScheduler A limits codeStart) := by
    constructor
    · simp
    · simp [initialScheduler]
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    0#u64 source (initialScheduler A limits codeStart) scheduler storage env accepted
  obtain ⟨raw,encoded,matched,valid,entryBounds,functions,types,codeCount,
    header,entries,codeBound,moduleBound⟩ := stream_run_source
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    SchedulerTracks (compiler_provenance ops law) 0#u64 source
    (initialScheduler A limits codeStart) scheduler env bytes environment code tailBytes coherent recombine initial run
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq,Prod.mk.injEq,true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame ops 0#u64 run.remaining.ready scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq,tailReady] at finalTail
  have sameTail : tail = run.remaining.tail := Option.some.inj finalTail
  exact ⟨raw,encoded,by simpa only [sameTail] using matched,functions,moduleBound⟩
end Itasca.Compiler

end

/-! ## CompilerLargeEnvironment -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- An oversized scanned environment is rejected before any compiler callback.
This covers custom compile limits larger than the validator's module cap. -/
theorem compiler_stream_large_environment {V : Type} (visitor : stream.StreamingVisitor V)
     (source : runtime.compiler.CompileSource)
    (bounds : SourceBounds source) (large : limits.MAX_MODULE_BYTES.val < source.code_start.val)
    (state : V) (storage : metadata.Env) :
    stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource visitor
      0#u64 source state storage = .ok (.Err .ModuleTooLarge,state,storage) := by
  obtain ⟨_,environment,bytes,rfl,decoded⟩ := WP.spec_imp_exists (source_environment_spec source bounds)
  have length : bytes.length = source.code_start.val := by
    simp only [Slice.length,decoded,sourceEnvironment,List.length_take]
    have bound := bounds.1.trans bounds.2
    change source.code_start.val ≤ source.bytes.val.length at bound
    omega
  obtain ⟨result,checked,post⟩ := WP.spec_imp_exists (limits.add_offset.spec 0#usize (Slice.len bytes))
  have rejected : result = .Err .ModuleTooLarge := by
    cases result with
    | Err error => exact congrArg core.result.Result.Err post.1
    | Ok total =>
      have bound := post.2
      have count := post.1
      simp only [show (0#usize).val = 0 from rfl,Slice.len_val] at count
      omega
  simp only [Itasca.stream.validate_streaming]
  simp only [environment]
  simp only [bind_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [checked,rejected]
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Itasca.Compiler

end

/-! ## InitializerTotalMappings -/

section

/-!
Normal return of element initializer values and the initializer mapping loops.
-/

/-! ## Initializer Total Element -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (space : initializerSize m + segment.init.val.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops m budget i ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + segment.init.val.length + 3 ⦄ := by
  exact runtime.compiler.initialize.lower_element.total ops law m budget i segment found space

end Itasca.Compiler

end

end

/-! ## InitializerTotal -/

section

/-!
Normal return of initializer emission and segment loops, composed into complete initializer lowering.
-/

/-! ## Initializer Total Emit -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- A single segment emits at most five instructions, one vector constant,
and one table-index pair. The bounds include rejected partial emissions. -/
@[step] theorem initializer_emit_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.env.elements.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max)
    (pairFits : function.indirect.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_element ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + 1 ⦄ := by
  exact runtime.compiler.initialize.emit_element.total ops law m budget function index bound codeFits poolFits pairFits

@[step] theorem initializer_emit_data_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_data ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  exact runtime.compiler.initialize.emit_data.total ops law m budget function index bound codeFits poolFits

end Itasca.Compiler

end

/-! ## Initializer Total -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Initializer lowering returns normally under its finite append headroom.
These quantitative input bounds concern internal vectors, not correctness of
compiled code or normal return of a subcomputation. Every allocator refusal,
instruction-budget rejection, and checker rejection is included. -/
@[step] theorem initializer_lower_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (mapSpace : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + initializerMappingCost m.module + 1 ⦄ := by
  exact runtime.compiler.initialize.lower.total ops law m budget mapSpace segmentSpace

/-- Driver-facing form: initializer maps are freshly empty, so only source
counts and the already compiled function count consume the retained allowance. -/
theorem initializer_lower_fresh_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (globals : m.global_initializers.val = [])
    (elements : m.element_initializers.val = [])
    (elementOffsets : m.element_offsets.val = [])
    (dataOffsets : m.data_offsets.val = [])
    (mapSpace : m.functions.val.length + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ _ => True ⦄ := by
  have headroom : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max := by
    simpa [initializerSize, globals, elements, elementOffsets, dataOffsets] using mapSpace
  apply WP.spec_mono (initializer_lower_total ops law m budget headroom segmentSpace)
  intros; trivial

end Itasca.Compiler

end

end

end

/-! ## SourceMetadataAndSegments -/

section

/-!
Proofs for Runtime / Compiler / Module.

This module collects SourceMetadataAndSegments, SourceBudget.
Each section documents its contracts and consumers.
-/

/-! ## SourceMetadataAndSegments -/

section

/-!
# Source Metadata And Segments

Cached source metadata and compiled data segments retain their independent source interpretation.
-/

/-! ## CompileCache -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Canonical accepted environment parsing establishes the exact imported and
defined index-space caches retained by the executable module. -/
theorem CompileWitness.cache_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable) :
    ∃ tables memories, Module.Environment.Cache w.env tables memories := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have decoded := metadata.validate_env_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.environment run.region w.env run.environmentLength run.decoded run.decode_environment
  have semantic := metadata.validate_env.semantic_spec run.environment
  rw [decoded, WP.spec_ok] at semantic
  obtain ⟨decls, represented, _, _, _, _⟩ := semantic
  exact ⟨decls.tables, decls.memories, represented.cache⟩

theorem CompileWitness.cache {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∃ tables memories, Module.Environment.Cache executable.module.env tables memories := by
  rw [(w.initializers law).1]
  exact w.cache_input

end Itasca.Compiler

end

/-! ## SegmentPayloadBounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Binary

private theorem vector_length_bound {α : Type} {R : α → List UInt8 → Prop} {values bytes}
    (encoded : WebAssembly.Binary.VecEncoding R values bytes) : values.length < 2^32 := by
  obtain ⟨count, entries, bounded, _, _⟩ := encoded
  exact (Itasca.Binary.Source.readerLeb bounded).value_lt

private theorem element_payload_bound {entry bytes}
    (encoded : WebAssembly.Binary.ElementEncoding entry bytes) : entry.init.length < 2^32 := by
  obtain ⟨_, _, _, _, hi, _⟩ := encoded
  exact vector_length_bound hi

private theorem data_payload_bound {entry bytes}
    (encoded : WebAssembly.Binary.DataEncoding entry bytes) : entry.init.length < 2^32 := by
  obtain ⟨_, h⟩ := WebAssembly.Binary.DataEncoding.init_vector encoded
  exact vector_length_bound h

private theorem rep_property {α : Type} {R : α → List UInt8 → Prop} {Q : α → Prop} {values bytes}
    (encoded : WebAssembly.Binary.Rep R values bytes) (property : ∀ value bytes, R value bytes → Q value) :
    ∀ value ∈ values, Q value := by
  induction encoded with
  | nil => simp
  | cons head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact property _ _ head
    · exact ih value member

private theorem padded_property {α : Type} {R : α → List UInt8 → Prop} {Q : α → Prop} {id values bytes}
    (encoded : WebAssembly.Binary.PaddedEncoding id (WebAssembly.Binary.VecEncoding R) [] values bytes)
    (property : ∀ value bytes, R value bytes → Q value) : ∀ value ∈ values, Q value := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, _, encoded, _⟩, _⟩ := content
    exact rep_property encoded property

/-- Binary vector prefixes bound every element and data payload, independently
of semantic typing and of the compiler's chosen instruction representation. -/
private theorem native_segment_payload_bounds {R raw bytes}
    (encoded : WebAssembly.Binary.ModuleEncodingWith R raw bytes) :
    (∀ element ∈ raw.elements, element.init.length < 2^32) ∧
    (∀ segment ∈ raw.data, segment.init.length < 2^32) := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, _, _⟩ := encoded
  exact ⟨padded_property hel (fun _ _ h => element_payload_bound h),
    padded_property hd (fun _ _ h => data_payload_bound h)⟩

theorem module_segment_payload_bounds {R raw bytes} (encoded : ModuleEncodingWith R raw bytes) :
    (∀ element ∈ raw.elements, element.init.length < 2^32) ∧
    (∀ segment ∈ raw.data, segment.init.length < 2^32) := by
  have native := Source.moduleEncodingWith (S := fun _ _ => True) (fun _ => trivial) encoded
  simpa [Source.rawModule, Source.element, Source.dataEntry, Source.bytes] using native_segment_payload_bounds native

/-- Payload bounds for the actual metadata retained by an accepted validator. -/
theorem validated_segment_payload_bounds {bytes module}
    (validated : Itasca.Module.Sound.Validated bytes module) :
    (∀ element ∈ module.env.elements.val, element.init.length < 2^32) ∧
    (∀ segment ∈ module.tail.data.val, segment.init.length < 2^32) := by
  obtain ⟨raw, encoded, _, matched, _⟩  := validated
  have bounds : (∀ e ∈ raw.elements, e.init.length < 2^32) ∧ (∀ d ∈ raw.data, d.init.length < 2^32) := by
    simpa [Source.rawModule, Source.element, Source.dataEntry, Source.bytes] using native_segment_payload_bounds encoded
  obtain ⟨elements, datas⟩ := bounds
  have he := congrArg Itasca.Binary.Module.elements matched.1
  have hd := congrArg Itasca.Binary.Module.data matched.1
  constructor
  · intro element member
    apply elements (Itasca.Module.Environment.rawElement element)
    rw [he]
    exact List.mem_map.mpr ⟨element, member, rfl⟩
  · intro segment member
    apply datas (Itasca.Module.Data.raw segment)
    rw [hd]
    exact List.mem_map.mpr ⟨segment, member, rfl⟩

/-- The public compiler supplies the payload bounds without an added count premise. -/
theorem compile_segment_payload_bounds {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (module : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with allocator bytes limits = .ok (.Ok module)) :
    (∀ element ∈ module.module.env.elements.val, element.init.length < 2^32) ∧
    (∀ segment ∈ module.module.tail.data.val, segment.init.length < 2^32) := by
  exact validated_segment_payload_bounds (compile_source_validated allocator law bytes limits module accepted).1
end Itasca.Compiler

end

/-! ## SourceInstantiation -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

private theorem mapped_two {α β γ δ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (h : β → γ → δ) : Map₂ h (xs.map f) (xs.map g) = xs.map (fun x => h (f x) (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [Map₂, List.map_cons, WebAssembly.List.ap, List.zipWith_cons_cons] using congrArg (h (f x) (g x) :: ·) ih

private theorem mapped_three {α β γ δ ε : Type} (xs : List α) (f : α → β) (g : α → γ)
    (h : α → δ) (combine : β → γ → δ → ε) :
    Map₃ combine (xs.map f) (xs.map g) (xs.map h) = xs.map (fun x => combine (f x) (g x) (h x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [Map₃, List.map_cons, WebAssembly.List.ap, List.zipWith_cons_cons] using congrArg (combine (f x) (g x) (h x) :: ·) ih

private theorem forall_three {α β γ δ : Type} (xs : List α) (f : α → β) (g : α → γ) (h : α → δ)
    (P : β → γ → δ → Prop) (checked : ∀ x ∈ xs, P (f x) (g x) (h x)) :
    Forall₃ P (xs.map f) (xs.map g) (xs.map h) := by
  induction xs with
  | nil => simp [Forall₃]
  | cons x xs ih =>
    have head := checked x (by simp)
    have tail := ih (fun a mem => checked a (by simp [mem]))
    simpa [Forall₃] using And.intro head tail

private theorem padded_count {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (encoded : Binary.PaddedEncoding id (Binary.VecEncoding R) [] values bytes) :
    values.length < 2^32 := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, bounded, _, _⟩, _⟩ := content
    exact bounded.value_lt

theorem module_segment_counts {R raw bytes}
    (encoded : Binary.ModuleEncodingWith R raw bytes) :
    raw.elements.length < 2^32 ∧ raw.data.length < 2^32 := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, _, _⟩ := encoded
  exact ⟨padded_count hel, padded_count hd⟩

private theorem evaluation_value_wf {before after : state} {expression : expr} {value : val}
    (evaluated : Eval_expr before expression after [value]) : wf_val value := by
  cases evaluated with
  | mk_Eval_expr _ _ final =>
    have valueSyntax := (Spec.wf_config_parts final).2 (admininstr_val value) (by simp [Map])
    cases value <;> simp only [admininstr_val] at valueSyntax <;> cases valueSyntax <;> constructor <;> assumption

private theorem evaluated_values_wf {α : Type} {originals : List α} {values : List val}
    {before after : state} {expression : α → expr}
    (evaluated : List.Forall₂ (fun original value => Eval_expr before (expression original) after [value]) originals values) :
    Forall wf_val values := by
  induction evaluated with
  | nil => simp [Forall]
  | cons first rest ih =>
    intro value present
    rcases List.mem_cons.mp present with rfl | present
    · exact evaluation_value_wf first
    · exact ih value present

/-- Canonical raw module syntax discharges the generated instantiation rule's
structural side conditions. Allocation and initializer evaluations are concrete
source judgments supplied by the corresponding implementation bridges. -/
theorem source_instantiate {raw : Binary.Module} {R bytes}
    (encoded : Binary.ModuleEncodingWith R raw bytes)
    (elaborates : Module.Elaboration.Elaborates raw (Module.Elaboration.moduleOf raw))
    (typed : Module_ok (Module.Elaboration.moduleOf raw))
    (s after : store) (externals : List externaddr) (inst initialModule : moduleinst)
    (importedFunctions importedGlobals : List Nat) (values : List val) (references : List (List ref))
    (importFunctions : fun_funcs externals importedFunctions) (importGlobals : fun_globals externals importedGlobals)
    (initialEq : initialModule = ⟨raw.types.map Translation.Environment.funcType,
      importedFunctions ++ (List.range (List.zipWith CodeEntry.function raw.functions raw.codes).length).map (fun index => s.FUNCS.length + index),
      importedGlobals, [], [], [], [], []⟩)
    (globalEval : List.Forall₂ (fun original value => Eval_expr ⟨s, ⟨[], initialModule⟩⟩
      (Module.Constants.expression original.init) ⟨s, ⟨[], initialModule⟩⟩ [value]) raw.globals values)
    (elementEval : List.Forall₂ (fun original values => List.Forall₂ (fun expression value =>
      Eval_expr ⟨s, ⟨[], initialModule⟩⟩ (Module.Constants.expression expression)
        ⟨s, ⟨[], initialModule⟩⟩ [val_ref value]) original.init values) raw.elements references)
    (allocated : fun_allocmodule s (Module.Elaboration.moduleOf raw) externals values references (after, inst))
    (storeWf : wf_store s) :
    fun_instantiate s (Module.Elaboration.moduleOf raw) externals
      ⟨⟨after, ⟨[], inst⟩⟩,
        (Spec.Segment.elementPrograms (raw.elements.map Module.Elaboration.element)).flatten.map admininstr_instr ++
        ((Spec.Segment.dataPrograms (raw.data.map Module.Data.translate)).flatten.map admininstr_instr ++
          (raw.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList)⟩ := by
  have single : ∀ data ∈ raw.data, Spec.Segment.singleMemoryData (Module.Data.translate data) := by
    intro data member
    exact source_datas_single_memory raw elaborates typed _ (List.mem_map.mpr ⟨data, member, rfl⟩)
  have afterWf : wf_store after := by cases allocated; assumption
  have instanceWf : wf_moduleinst inst := by cases allocated; assumption
  have valuesWf := evaluated_values_wf globalEval
  have initialWf : wf_moduleinst initialModule := by
    rw [initialEq]
    constructor
    simp [Forall]
  have sourceWf : wf_module (Module.Elaboration.moduleOf raw) := by cases typed; assumption
  have globalsWf : Forall wf_global (raw.globals.map Module.Constants.global) := by cases sourceWf; assumption
  have elementsWf : Forall wf_elem (raw.elements.map Module.Elaboration.element) := by cases sourceWf; assumption
  have datasWf : Forall wf_data (raw.data.map Module.Data.translate) := by cases sourceWf; assumption
  have startWf : Forall (fun index => wf_start (.START index)) (raw.start.map (fun index => uN.mk_uN index.val)).toList := by
    have h : Forall wf_start (raw.start.map Module.Elaboration.start).toList := by cases sourceWf; assumption
    cases hs : raw.start <;> simpa [Forall, Module.Elaboration.start, hs] using h
  have counts := module_segment_counts encoded
  have payloads := module_segment_payload_bounds encoded
  obtain ⟨runElements, programsE⟩ := Spec.Segment.element_programs (raw.elements.map Module.Elaboration.element)
    (by simpa using Nat.le_of_lt counts.1) (by
      intro segment mem
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp mem
      exact ⟨elementsWf _ (List.mem_map.mpr ⟨original,present,rfl⟩), by
        simpa [Spec.Segment.elementSize, Module.Elaboration.element] using payloads.1 original present⟩)
  obtain ⟨runDatas, programsD⟩ := Spec.Segment.data_programs (raw.data.map Module.Data.translate)
    (by simpa using Nat.le_of_lt counts.2) (by
      intro segment mem
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp mem
      exact ⟨datasWf _ (List.mem_map.mpr ⟨original,present,rfl⟩), by
        simpa [Spec.Segment.dataSize, Module.Data.translate] using payloads.2 original present, single original present⟩)
  have globalRun : List.Forall₂ (fun expression value => Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression
      ⟨s, ⟨[], initialModule⟩⟩ [value]) (raw.globals.map (fun original => Module.Constants.expression original.init)) values :=
    List.forall₂_map_left_iff.mpr globalEval
  have elementRun : List.Forall₂ (fun expressions values => List.Forall₂ (fun expression value =>
      Eval_expr ⟨s, ⟨[], initialModule⟩⟩ expression ⟨s, ⟨[], initialModule⟩⟩ [val_ref value]) expressions values)
      (raw.elements.map (fun original => original.init.map Module.Constants.expression)) references := by
    apply List.forall₂_map_left_iff.mpr
    exact elementEval.imp (fun _ _ h => List.forall₂_map_left_iff.mpr h)
  have startIndexWf : Forall (wf_uN 32) (raw.start.map (fun index => uN.mk_uN index.val)).toList := by
    intro index mem
    have h := startWf index mem
    cases h; assumption
  have desired : fun_instantiate s (Module.Elaboration.moduleOf raw) externals
      ⟨⟨after, ⟨[], inst⟩⟩,
        (Spec.Segment.elementPrograms (raw.elements.map Module.Elaboration.element)).flatten.map admininstr_instr ++
        ((Spec.Segment.dataPrograms (raw.data.map Module.Data.translate)).flatten.map admininstr_instr ++
          ((raw.start.map (fun index => uN.mk_uN index.val)).map admininstr.CALL).toList)⟩ := by
    apply Spec.instantiate_source (initialModule := initialModule) s after (Module.Elaboration.moduleOf raw) externals
      (raw.types.map Translation.Environment.funcType) (raw.imports.map (Module.Elaboration.importDecl raw.types))
      (List.zipWith CodeEntry.function raw.functions raw.codes) (raw.globals.map Module.Constants.global)
      (raw.tables.map Module.Elaboration.table) (raw.memories.map Module.Elaboration.memory)
      (raw.elements.map Module.Elaboration.element) (raw.data.map Module.Data.translate)
      (raw.start.map (fun index => .mk_uN index.val)) (raw.exports.map Module.Elaboration.exportDecl)
      (raw.globals.map (fun original => Module.Constants.expression original.init))
      (raw.globals.map (fun original => Translation.globalType original.gtype))
      (raw.elements.map (fun original => Module.Segments.elementMode original.mode))
      (raw.elements.map (fun original => original.init.map Module.Constants.expression))
      (raw.elements.map (fun original => Translation.referenceType original.elem)) values references importedFunctions importedGlobals inst
      (Spec.Segment.elementPrograms (raw.elements.map Module.Elaboration.element))
      (Spec.Segment.dataPrograms (raw.data.map Module.Data.translate))
    · simp only [Module.Elaboration.moduleOf, List.map_map, Option.map_map, Function.comp_def]
      rfl
    · rw [mapped_two]; rfl
    · rw [mapped_three]; rfl
    · exact importFunctions
    · exact importGlobals
    · exact initialEq
    · simpa using globalRun.length_eq
    · exact fun _ mem => List.forall₂_zip globalRun mem
    · simpa using elementRun.length_eq
    · exact fun _ mem => (List.forall₂_zip elementRun mem).length_eq
    · exact fun _ mem => fun _ member => List.forall₂_zip (List.forall₂_zip elementRun mem) member
    · exact allocated
    · exact runElements
    · exact runDatas
    · exact valuesWf
    · exact afterWf
    · exact instanceWf
    · exact programsE
    · exact programsD
    · exact Spec.Segment.initialization_config_wf _ _ _ _ _ afterWf instanceWf programsE programsD startIndexWf
    · exact sourceWf
    · simp
    · have h : List.Forall₂ (fun expression ty => wf_global (.GLOBAL ty expression))
          (raw.globals.map (fun original => Module.Constants.expression original.init))
          (raw.globals.map (fun original => Translation.globalType original.gtype)) := by
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact List.forall₂_same.mpr (fun original mem => globalsWf _ (List.mem_map.mpr ⟨original,mem,rfl⟩))
      exact fun _ mem => List.forall₂_zip h mem
    · simp
    · simp
    · apply forall_three
      intro original mem
      exact elementsWf _ (List.mem_map.mpr ⟨original,mem,rfl⟩)
    · exact startWf
    · exact initialWf
    · exact storeWf
    · simpa using Nat.le_of_lt counts.1
    · simpa using Nat.le_of_lt counts.2
  simpa only [Option.map_map, Function.comp_def] using desired
end Itasca.Compiler

end

/-! ## CompileDataCount -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual accepted tail validation agrees with every declared data count. -/
theorem CompileWitness.data_count_input {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable) :
    ∀ count, w.env.data_count = some count → count.val = w.tail.data.val.length := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted
    runtime.compiler.CompileSource.Insts.ItascaStreamStreamingSource
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
    0#u64 {bytes, code_start := w.codeStart, code_end := w.codeEnd}
    (initialScheduler A limits w.codeStart) w.scheduler w.initialEnv w.env w.validated
  have tailDecoded := metadata.validate_tail_with.accepted_erase
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator).metadataModuleVisitorInst
    run.remaining.tailBytes 0#usize w.env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have tailSemantic := metadata.validate_tail.spec run.remaining.tailBytes 0#usize w.env (by simp)
  rw [tailDecoded, WP.spec_ok] at tailSemantic
  obtain ⟨_, _, count⟩ := tailSemantic
  have readyEq : run.remaining.ready = {run.remaining.decodedTail with tail := some run.remaining.tail} := by
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.project_tail_ready.eq,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready.eq,
      Result.ok.injEq, Prod.mk.injEq, true_and] using run.remaining.ready_call.symm
  have drained := compiler_drain_frame allocator 0#u64 run.remaining.ready w.scheduler
    run.remaining.pending run.remaining.remaining run.remaining.drain_call
  have finalTail := congrArg runtime.compiler.CompileScheduler.tail drained
  simp only [readyEq, w.tailReady] at finalTail
  have sameTail : w.tail = run.remaining.tail := Option.some.inj finalTail
  simpa only [sameTail] using count

/-- Initializer lowering retains the canonical data-count agreement. -/
theorem CompileWitness.data_count {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ∀ count, executable.module.env.data_count = some count →
      count.val = executable.module.tail.data.val.length := by
  rw [(w.initializers law).1]
  exact w.data_count_input

end Itasca.Compiler

end

end

/-! ## SourceBudget -/

section

/-!
# Computed source budgets supply internal compilation demands

Only this adapter relates the public numerical budget to metadata caches,
preparation witnesses, reservation categories and initializer bookkeeping.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Binary Module.Environment

private theorem member_le_max {values : List Nat} {value : Nat} (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact (ih member).trans (Nat.le_max_right _ _)

private theorem signature_widths {signature : wasm_types.FuncType}
    (valid : CodeEntry.FuncTypeWithinLimits signature) :
    signatureSlots signature.params.val ≤ U32.max ∧ signatureSlots signature.results.val ≤ U32.max := by
  have params := Representation.slots_le_twice_length (signature.params.val.map Translation.valueType)
  have results := Representation.slots_le_twice_length (signature.results.val.map Translation.valueType)
  simp only [List.length_map] at params results
  rcases valid.bounds with ⟨paramLimit, resultLimit⟩
  unfold signatureSlots
  scalar_tac

private theorem cached_member {types : List wasm_types.FuncType} {indices signatures}
    (cache : List.Forall₂ (Resolves types) indices signatures) {signature}
    (member : signature ∈ signatures) : signature ∈ types := by
  induction cache with
  | nil => cases member
  | cons head _ ih =>
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨bound, rfl⟩ := head
      exact List.getElem_mem bound
    · exact ih member

private theorem vector_count {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (encoded : PaddedEncoding id (VecEncoding R) [] values bytes) : values.length ≤ U32.max := by
  obtain ⟨_, _, _, encodedSection, _⟩ := encoded
  cases encodedSection with
  | absent => exact Nat.zero_le _
  | present content =>
    obtain ⟨_, _, _, ⟨_, _, count, _, _⟩, _⟩ := content
    have bounded := count.value_lt
    scalar_tac

private theorem segment_counts {R raw bytes} (encoded : ModuleEncodingWith R raw bytes) :
    raw.elements.length ≤ U32.max ∧ raw.data.length ≤ U32.max := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, elements, _, _, datas, _, _, _⟩ := encoded
  exact ⟨vector_count elements, vector_count datas⟩

/-- Deterministic source eligibility supplies every old internal demand. No
successful parser/compiler execution is needed to construct this adapter. -/
theorem CompileEligible.internal {bytes : Slice U8} {raw : Binary.Module}
    {limits : runtime.compiler.CompileLimits} (eligible : CompileEligible bytes raw limits)
    (valid : ValidCompilationSource bytes raw) :
    InternalCompileEligible bytes raw limits (compilationBudget bytes.length raw).allocation := by
  refine ⟨eligible.moduleBytes, ?_⟩
  intro env tail matched
  have types : env.types.val = raw.types := (congrArg Binary.Module.types matched.1).symm
  have functions : env.func_type_indices.val = raw.functions := (congrArg Binary.Module.functions matched.1).symm
  have imports : env.imports.val.length = raw.imports.length := by
    have same := congrArg (fun m : Binary.Module => m.imports.length) matched.1
    simpa only [Module.Elaboration.fromEnv, List.length_map] using same.symm
  have globals : env.globals.val = raw.globals := (congrArg Binary.Module.globals matched.1).symm
  have elements : env.elements.val.map rawElement = raw.elements := (congrArg Binary.Module.elements matched.1).symm
  have datas : tail.data.val.map Module.Data.raw = raw.data := (congrArg Binary.Module.data matched.1).symm
  have elementCount : env.elements.length = raw.elements.length := by
    simpa only [List.length_map] using congrArg List.length elements
  have dataCount : tail.data.length = raw.data.length := by
    simpa only [List.length_map] using congrArg List.length datas
  let b := if raw.functions.length = 0 then 0 else Nat.min bytes.length Itasca.limits.MAX_FUNCTION_BYTES.val
  let l := if raw.functions.length = 0 then 0 else
    (raw.types.map (fun signature => signature.params.val.length)).foldr max 0 + Itasca.limits.MAX_LOCALS.val
  let p := 500 * b
  let mappings := 2 * raw.globals.length + (raw.elements.map (fun e => e.init.length + 3)).sum + 2 * raw.data.length
  let segments := 5 * (raw.elements.length + raw.data.length) + 1
  let bound := (compilationBudget bytes.length raw).allocation
  have reserves : 4 ≤ bound ∧ raw.types.length ≤ bound ∧ raw.imports.length + raw.functions.length ≤ bound ∧
      3 * b + 3 ≤ bound ∧ l ≤ bound ∧ p ≤ bound ∧ raw.functions.length + mappings + 1 ≤ bound ∧ segments ≤ bound := by
    dsimp only [bound, compilationBudget, b, l, p, mappings, segments]
    omega
  have mappingEq : initializerMappingCost ⟨env, tail⟩ = mappings := by
    simp only [initializerMappingCost, initializerElementCost, mappings, globals, ← elements, ← datas,
      List.map_map, List.length_map, rawElement, Module.Data.raw, Function.comp_def]
  have cacheCount : env.func_types.length ≤ raw.imports.length + raw.functions.length := by
    have same := matched.2.funcs.length_eq
    have imported : (importedFuncs env.imports.val).length ≤ env.imports.val.length :=
      List.length_filterMap_le _ _
    simp only [List.length_append, functions] at same
    change env.func_types.val.length ≤ _
    omega
  have widths : ∀ signature ∈ env.types.val,
      signatureSlots signature.params.val ≤ U32.max ∧ signatureSlots signature.results.val ≤ U32.max := by
    intro signature member
    exact signature_widths (valid.signatures signature (types ▸ member))
  have countBounds := segment_counts valid.encoding.encoding
  have payloadBounds := module_segment_payload_bounds valid.encoding.encoding
  refine ⟨b, l, p, ?_⟩
  constructor
  · refine ⟨?_, ?_, widths, ?_, ?_, ?_, ?_⟩
    · simpa only [compilationBudget, alloc.vec.Vec.length, functions] using eligible.functions
    · simpa only [compilationBudget, alloc.vec.Vec.length, types] using eligible.types
    · intro signature member
      exact (widths signature (cached_member matched.2.funcs member)).1
    · simpa only [alloc.vec.Vec.length, types] using reserves.2.1
    · omega
    · simpa only [alloc.vec.Vec.length, functions] using
        (Nat.le_add_left raw.functions.length raw.imports.length).trans reserves.2.2.1
  · refine ⟨?_, ?_, ?_, ?_, reserves.2.2.2.1, reserves.2.2.2.2.1, reserves.2.2.2.2.2.1, ?_⟩
    · dsimp only [b]
      split
      · exact Nat.zero_le _
      · exact Nat.min_le_right _ _
    · simpa only [compilationBudget, b, l, functions] using eligible.branches
    · simpa only [compilationBudget, b, l, functions] using eligible.controls
    · simpa only [compilationBudget, b, l, functions] using eligible.locals
    · exact eligible.frameWords
  · intro index member signature found
    have nonempty : raw.functions.length ≠ 0 := by
      rw [functions] at member
      exact (List.length_pos_of_mem member).ne'
    have memberType := List.mem_of_getElem? found
    have params : signature.params.val.length ≤
        (raw.types.map (fun signature => signature.params.val.length)).foldr max 0 :=
      member_le_max (List.mem_map.mpr ⟨signature, types ▸ memberType, rfl⟩)
    dsimp only [b, l, p]
    simp only [nonempty, ↓reduceIte]
    exact ⟨Nat.le_refl _, Nat.add_le_add_right params _, Nat.le_refl _⟩
  · simpa only [compilationBudget, b, sourceInitializerInstructions, mappingEq, mappings, elementCount, dataCount, functions, Nat.add_assoc] using eligible.instructions
  · have reserve := reserves.2.2.2.2.2.2.1
    rw [functions, mappingEq]
    exact reserve.trans eligible.allocation
  · simpa only [functions, mappingEq] using reserves.2.2.2.2.2.2.1
  · omega
  · rw [elementCount, dataCount]
    exact reserves.2.2.2.2.2.2.2.trans eligible.allocation
  · simpa only [elementCount, dataCount] using reserves.2.2.2.2.2.2.2
  · simpa only [elementCount] using countBounds.1
  · simpa only [dataCount] using countBounds.2
  · intro segment member
    have bound := payloadBounds.1 (rawElement segment) (elements ▸ List.mem_map.mpr ⟨segment, member, rfl⟩)
    change segment.init.val.length ≤ U32.max
    change segment.init.val.length < 2^32 at bound
    scalar_tac
  · intro segment member
    have bound := payloadBounds.2 (Module.Data.raw segment) (datas ▸ List.mem_map.mpr ⟨segment, member, rfl⟩)
    change segment.init.val.length ≤ U32.max
    change segment.init.val.length < 2^32 at bound
    scalar_tac
  · exact reserves.1

end Itasca.Compiler

end

end
