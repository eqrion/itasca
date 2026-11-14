import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Module.CodeRegionContracts
import Itasca.Runtime.Compiler.Module.CollectionContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.SignatureCapture
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Stream.Header
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Stream.InvariantRetirement
import Itasca.Stream.SplitComplete

/-!
Sections, each formerly its own module: EnvironmentFrame, CollectFunctions, SchedulerSubmission, SchedulerSafety, CompileEntryTotal, CompileAssembly, CompilerDrain, CompileSource, CodeRegionComplete.
-/

/-! ## EnvironmentFrame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

/-- Environment preparation does not alter queued workers, the source origin,
or the tail handoff. This statement follows from actual successful callbacks. -/
theorem compiler_environment_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (config : stream.Config)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
      allocator before env = .ok (.Ok config, after)) : schedulerFrame after = schedulerFrame before := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.inv allocator before after env config accepted

end Itasca.Runtime.Compiler

end

/-! ## CollectFunctions -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## SchedulerSubmission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Metadata captured before any function compilation is fixed across all
actual entry calls in a submitted batch. -/
def schedulerStatic {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.signatures, scheduler.func_param_slots, scheduler.code_start)

theorem CompileEntryWitness.static {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch) :
    schedulerStatic after = schedulerStatic before := by rw [w.published]; rfl

theorem CompileEntries.static {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch) :
    schedulerStatic after = schedulerStatic before := by
  induction run with
  | nil => rfl
  | next entry rest ih =>
    obtain ⟨w⟩ := compile_entry_accepted _ _ _ _ _ entry
    exact ih.trans w.static

end Itasca.Runtime.Compiler

end

/-! ## SchedulerSafety -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## CompileEntryTotal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Dispatch, compiler construction, final bytecode checking, and indexed
publication return normally. The remaining body obligation names only the
fresh compiler reached by this actual issued entry. -/
theorem compiler_entry_total_of_validation {A : Type} (ops : runtime.platform.Alloc A)
    (before : CompileScheduler A) (issued : StreamBatch.Issued) (batch : stream.CodeBatch)
    (bounded : issued.Bounded) (reachable : StreamBatch.Reachable issued batch)
    (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (validation : ∀ (entry : stream.CodeEntry) (dispatched : stream.CodeBatch)
      (batchStart : Usize) (initial : FunctionCompiler A),
      stream.CodeBatch.next_entry batch = .ok (.Ok entry,dispatched) →
      (before.code_start + dispatched.code_offset : Result Usize) = .ok batchStart →
      FunctionCompiler.new ops (alloc.vec.Vec.deref before.signatures)
        (alloc.vec.Vec.deref before.func_param_slots) {before.budget with marker := ()} batchStart = .ok initial →
      stream.CodeBatch.validate_func (FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        dispatched entry.index initial ⦃ _ => True ⦄) :
    runtime.compiler.CompileScheduler.compile_entry ops before batch ⦃ _ => True ⦄  := by
  exact runtime.compiler.CompileScheduler.compile_entry.total ops before issued batch
    bounded reachable origin validation

end Itasca.Runtime.Compiler

end

/-! ## CompileAssembly -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

def initialScheduler (A : Type) (limits : runtime.compiler.CompileLimits) (codeStart : Usize) :
    runtime.compiler.CompileScheduler A :=
  { signatures := alloc.vec.Vec.new _, func_param_slots := alloc.vec.Vec.new _,
    completed := alloc.vec.Vec.new _, functions := alloc.vec.Vec.new _, tail := none,
    code_start := codeStart,
    budget := {marker := (), limits, instructions := 0#usize, branches := 0#usize, controls := 0#usize, locals := 0#usize, error := none} }

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
  validated : stream.validate_streaming runtime.compiler.CompileSource.Insts.ItascaStreamSource
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
      stream.validate_streaming CompileSource.Insts.ItascaStreamSource
        (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64
        {bytes,code_start := codeStart,code_end := codeEnd}
        (initialScheduler A limits codeStart) storage ⦃ out =>
          True ⦄)
    (lowering : ∀ (codeStart codeEnd : Usize) (storage env : metadata.Env)
      (scheduler : CompileScheduler A) (tail : metadata.Tail)
      (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
      (budget : Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)),
      codeStart.val ≤ codeEnd.val ∧ codeEnd.val ≤ bytes.length →
      stream.validate_streaming CompileSource.Insts.ItascaStreamSource
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

end Itasca.Runtime.Compiler

end

/-! ## CompilerDrain -/

section

/-!
Compiler worker provenance and drain preservation. SchedulerTracks records issued worker origins through queue operations and final draining.
-/

/-! ## Compiler Provenance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca

/-- Every completed worker comes from one issued batch in a history with unique
batch identifiers. The history is an internal invariant of the actual driver. -/
structure SchedulerTracks {A : Type} (_id : U64) (history : List StreamBatch.Issued)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  unique : ∀ left ∈ history, ∀ right ∈ history, left.batch_id = right.batch_id → left = right
  workers : ∀ batch ∈ scheduler.completed.val, ∃ issued ∈ history, StreamBatch.Reachable issued batch

theorem SchedulerTracks.queue {A : Type} {id history} {before after : runtime.compiler.CompileScheduler A}
    (tracked : SchedulerTracks id history before) (same : after.completed = before.completed) :
    SchedulerTracks id history after := by
  exact ⟨tracked.unique, by simpa only [same] using tracked.workers⟩

/-- The concrete compiler satisfies the canonical streaming scheduler's
provenance contract. Allocation decisions remain unrestricted. -/
theorem compiler_provenance {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) :
    StreamScheduler.Provenance
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
end Itasca.Runtime.Compiler

end

/-! ## Compiler Drain -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

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
end Itasca.Runtime.Compiler

end

end

/-! ## CompileSource -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca

/-- The concrete source scanner and compiler scheduler discharge all embedding
premises of the existing validator's accepted-module theorem. -/
theorem CompileWitness.source_validated {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) :
    ModuleSound.Validated bytes executable.module ∧ bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
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
  have coherent : StreamSource.Coherent runtime.compiler.CompileSource.Insts.ItascaStreamSource source
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
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
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
    ModuleSound.Validated bytes executable.module ∧
      bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val := by
  obtain ⟨w⟩ := compile_accepted allocator bytes limits executable accepted
  obtain ⟨validated, size⟩ := w.source_validated law
  exact ⟨validated, size⟩
end Itasca.Runtime.Compiler

end

/-! ## CodeRegionComplete -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca ModuleBinary
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
    (h : CustomsEncoding bytes) {pos next : Usize} (hb : Wasm1.BytesAt data pos bytes next) :
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
    (h : ModuleEnv.Chain raw n bytes) {pos next : Usize}
    (hb : Wasm1.BytesAt data pos bytes next) :
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
        At (SectionEncoding id (fun u bs => ModuleEnv.Payload raw (sectionRank id).val u bs)) data afterCustoms () middle
        from ⟨_, hs, hsection⟩).section_split
      rw [compiler_split_skip_section data afterCustoms content middle id hh (by
        have hrange := sectionRank_prefix (id := id) (by omega) (by omega)
        omega)]
      exact ih hrest

theorem compiler_split_skip_prefix {data : Slice U8} {decls next}
    (h : At (fun ds bs => ModuleEnv.PrefixEncoding ds bs) data 0#usize decls next) :
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
    (h : ModuleLayout.Layout data raw decls codePos tailPos) :
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
theorem compiler_code_region_eq_stream (data : Slice U8) (raw : ModuleBinary.Module)
    (encoded : ModuleEncodingWithinLimits raw data.val) :
    runtime.compiler.code_region data = Itasca.stream.find_code_region data := by
  obtain ⟨decls,codeStart,codeEnd,layout⟩ := ModuleLayout.normalize data raw encoded
  rw [compiler_code_region_complete_layout layout,Itasca.stream.find_code_region.complete_layout layout]

end Itasca.Runtime.Compiler

end
