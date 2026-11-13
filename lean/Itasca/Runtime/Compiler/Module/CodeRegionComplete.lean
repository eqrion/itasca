import Itasca.Runtime.Compiler.Module.CompileSubmit
import Itasca.Stream.Scheduler
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Stream.BatchBounds
import Itasca.Stream.DriverSound
import Itasca.Stream.SplitComplete

/-!
Sections, each formerly its own module: EnvironmentFrame, CollectFunctions, SchedulerSubmission, SchedulerSafety, CompileEntryTotal, CompileAssembly, CompilerDrain, CompileSource, CodeRegionComplete.
-/

/-! ## EnvironmentFrame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

def schedulerFrame {A : Type} (scheduler : runtime.compiler.CompileScheduler A) :=
  (scheduler.completed, scheduler.tail, scheduler.code_start)

theorem capture_signature_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error)
    (run : runtime.compiler.CompileScheduler.capture_signature allocator before env index = .ok (result, after)) :
    schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.capture_signature at run
  obtain ⟨types, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨signature, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨params, _, run⟩ := bind_ok_inv _ _ _ run
  cases params with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    exact congrArg schedulerFrame run.2.symm
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨results, _, run⟩ := bind_ok_inv _ _ _ run
    cases results with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      exact congrArg schedulerFrame run.2.symm
    | Ok results =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
      obtain ⟨⟨status, budget, signatures⟩, _, run⟩ := bind_ok_inv _ _ _ run
      obtain ⟨_, _, run⟩ := bind_ok_inv _ _ _ run
      have same := congrArg Prod.snd (Result.ok_injective run)
      simpa [schedulerFrame] using congrArg schedulerFrame same.symm

theorem capture_func_slots_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error)
    (run : runtime.compiler.CompileScheduler.capture_func_slots allocator before env index = .ok (result, after)) :
    schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots at run
  obtain ⟨types, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨signature, _, run⟩ := bind_ok_inv _ _ _ run
  obtain ⟨params, _, run⟩ := bind_ok_inv _ _ _ run
  cases params with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    exact congrArg schedulerFrame run.2.symm
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨⟨status, budget, slots⟩, _, run⟩ := bind_ok_inv _ _ _ run
    obtain ⟨_, _, run⟩ := bind_ok_inv _ _ _ run
    have same := congrArg Prod.snd (Result.ok_injective run)
    simpa [schedulerFrame] using congrArg schedulerFrame same.symm

theorem environment_loop0_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans
          (capture_signature_frame allocator before middle env index nextResult entry)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

theorem environment_loop1_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.compiler.CompileScheduler A) (env : metadata.Env) (index : Usize)
    (result : core.result.Result Unit error.Error) (output)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      allocator before env index result = .ok output) :
    (output.2.2.1, output.2.2.2.2.1, output.2.2.2.2.2.1) = schedulerFrame before := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1 at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
            allocator middle env nextIndex nextResult = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body, Itasca.metadata.Env.impl.func_types, core.result.Result.is_ok] using tail
        exact (ih _ smaller middle nextIndex nextResult tail' rfl).trans
          (capture_func_slots_frame allocator before middle env index nextResult entry)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl

/-- Environment preparation does not alter queued workers, the source origin,
or the tail handoff. This statement follows from actual successful callbacks. -/
theorem compiler_environment_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (env : metadata.Env) (config : stream.Config)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
      allocator before env = .ok (.Ok config, after)) : schedulerFrame after = schedulerFrame before := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready at accepted
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok] at accepted
  split at accepted
  · simp [runtime.compiler.Budget.reject] at accepted
  · simp only [Itasca.metadata.Env.impl.types, bind_ok] at accepted
    split at accepted
    · simp [runtime.compiler.Budget.reject] at accepted
    · obtain ⟨⟨signatures, slots, completed, functions, tail, start, budget, status⟩, loop0, rest⟩ :=
        bind_ok_inv _ _ _ accepted
      have frame0 := environment_loop0_frame allocator before env 0#usize (.Ok ()) _ loop0
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨signatures1, slots1, completed1, functions1, tail1, start1, budget1, status1⟩, loop1, rest⟩ :=
          bind_ok_inv _ _ _ rest
        have frame1 := environment_loop1_frame allocator
          ⟨signatures, slots, completed, functions, tail, start, budget⟩ env 0#usize (.Ok ()) _ loop1
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨functions2, budget2, status2⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unit =>
            cases unit
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              Result.ok.injEq, Prod.mk.injEq] at rest
            obtain ⟨_, output⟩ := rest
            subst after
            exact frame1.trans frame0
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
  unfold runtime.compiler.take_function
  step as ⟨value, back, lookup, restore⟩
  cases value with
  | none =>
    simp [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      restore, alloc.vec.Vec.set_val_eq]
  | some function =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push allocator law budget functions function capacity
      as ⟨result, afterBudget, afterFunctions, pushed⟩
    rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [WP.spec_ok, restore, alloc.vec.Vec.set_val_eq, List.length_set]
      refine ⟨True.intro, fun _ => ⟨function, ?_, True.intro, appended⟩⟩
      rw [List.getElem?_eq_getElem bound, ← lookup]
    · simp [restore, alloc.vec.Vec.set_val_eq]

/-- The pending suffix retains its source indices; the output is exactly the
already collected prefix, with no missing, duplicate, or reordered function. -/
def CollectionPrefix (original : List (Option runtime.bytecode.CompiledFunction))
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Nat) : Prop :=
  original.take index = functions.val.map some ∧ pending.val.drop index = original.drop index

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
  unfold runtime.compiler.collect_functions_loop
  apply loop.spec_decr_nat (fun state => original.length - state.2.2.2.1.val)
    (fun state => state.2.1.val.length = original.length ∧ state.2.2.2.1.val ≤ original.length ∧
      (state.2.2.2.2 = .Ok () → CollectionPrefix original state.2.1 state.2.2.1 state.2.2.2.1.val))
  · rintro ⟨currentBudget, currentPending, currentFunctions, currentIndex, status⟩ ⟨length, bound, prefixInvariant⟩
    dsimp only at length bound prefixInvariant
    unfold runtime.compiler.collect_functions_loop.body
    dsimp only
    split
    · rename_i more
      have inbounds : currentIndex.val < currentPending.val.length := by scalar_tac
      have originalBound : currentIndex.val < original.length := by omega
      cases status with
      | Err error => simp [core.result.Result.is_ok]
      | Ok acceptedUnit =>
        cases acceptedUnit
        obtain ⟨collected, remaining⟩ := prefixInvariant rfl
        have collectedLength := congrArg List.length collected
        simp only [List.length_take, List.length_map, Nat.min_eq_left bound] at collectedLength
        have capacity : currentFunctions.val.length < Usize.max := by
          have := currentPending.property
          omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with take_function_spec allocator law currentBudget currentPending currentIndex currentFunctions
          inbounds capacity as ⟨nextStatus, nextBudget, nextPending, nextFunctions, sameLength, taken⟩
        step as ⟨nextIndex, nextEq⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact sameLength.trans length
        · scalar_tac
        · intro success
          obtain ⟨function, found, pendingEq, appended⟩ := taken success
          have lookup := congrArg (fun values => values[0]?) remaining
          simp only [List.getElem?_drop, Nat.add_zero] at lookup
          have originalFound : original[currentIndex.val]? = some (some function) := lookup.symm.trans found
          have element := (List.getElem?_eq_some_iff.mp originalFound).2
          constructor
          · rw [nextEq, List.take_succ_eq_append_getElem originalBound, element, collected, appended]
            simp
          · rw [nextEq, pendingEq, List.drop_set_of_lt (Nat.lt_succ_self _)]
            have tail := congrArg (List.drop 1) remaining
            simpa only [List.drop_drop] using tail
        · scalar_tac
    · rename_i finished
      have indexEnd : currentIndex.val = original.length := by scalar_tac
      simp only [WP.spec_ok]
      intro success
      obtain ⟨collected, _⟩ := prefixInvariant success
      simpa only [indexEnd, List.take_length] using collected
  · exact ⟨length, bound, invariant⟩

/-- Actual collection succeeds exactly in source order. The final pending
vector is internal; callers receive the dense vector with every original slot. -/
@[step] theorem collect_functions_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (budget : runtime.compiler.Budget A)
    (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction)) :
    runtime.compiler.collect_functions allocator budget pending ⦃ out =>
      ∀ functions, out.1 = .Ok functions → pending.val = functions.val.map some ⦄ := by
  unfold runtime.compiler.collect_functions
  step with collect_functions_loop_spec allocator law pending.val budget pending
    (alloc.vec.Vec.new _) 0#usize (.Ok ()) rfl (by simp)
    (by simp [CollectionPrefix, alloc.vec.Vec.new]) as ⟨afterBudget, afterPending, functions, status, collected⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok acceptedUnit =>
    cases acceptedUnit
    simp [core.result.Result.Insts.CoreOpsTry.branch, collected rfl]

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
  unfold CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
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
    CompileScheduler.compile_entry ops before batch ⦃ _ => True ⦄ := by
  have identity := reachable.validation.1
  obtain ⟨_,_,_,_,_,first,count⟩ := identity
  have fits : batch.first_func.val + batch.num_funcs.val ≤ Usize.max := by
    rw [first,count]
    exact bounded.2.1.trans issued.env.func_type_indices.property
  obtain ⟨⟨result,dispatched⟩,dispatch⟩ := stream.CodeBatch.next_entry.total batch fits
  unfold CompileScheduler.compile_entry
  rw [dispatch]
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok entry =>
    have reached := StreamBatch.Reachable.dispatch reachable dispatch
    have identity := reached.validation.1
    obtain ⟨_,_,_,code,offset,_,_⟩ := identity
    have cap : limits.MAX_MODULE_BYTES.val + limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
      simp only [limits.MAX_MODULE_BYTES]
      scalar_tac
    have startFits : before.code_start.val + dispatched.code_offset.val ≤ Usize.max := by
      rw [offset]
      have := bounded.2.2
      omega
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      uncurry_apply_pair, Budget.copy_state,Itasca.stream.CodeBatch.impl.code_offset]
    obtain ⟨batchStart,startRun,startEq⟩ := WP.spec_imp_exists (Usize.add_spec (x := before.code_start) (y := dispatched.code_offset) startFits)
    rw [startRun]
    simp only [bind_ok,uncurry_apply_pair]
    obtain ⟨initial,created,_⟩ := WP.spec_imp_exists (compiler_new ops
      (alloc.vec.Vec.deref before.signatures) (alloc.vec.Vec.deref before.func_param_slots)
      {before.budget with marker := ()} batchStart)
    rw [created]
    simp only [bind_ok,uncurry_apply_pair]
    obtain ⟨⟨status,worker,final⟩,validated,_⟩ := WP.spec_imp_exists
      (validation entry dispatched batchStart initial dispatch startRun created)
    rw [validated]
    simp only [bind_ok,uncurry_apply_pair]
    obtain ⟨⟨result,budget⟩,finished,_⟩ := WP.spec_imp_exists (compiler_finish_total ops final status)
    rw [finished]
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok function =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,uncurry_apply_pair]
      split
      · simp
      · step as ⟨existing, found⟩
        cases existing with
        | some value => simp [core.option.Option.is_some]
        | none =>
          simp only [Option.isSome,Bool.false_eq_true,↓reduceIte]
          step

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
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaMetadataModuleVisitor.on_custom_section,
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
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked
  · intro id history before tail after tracked accepted
    have same : {before with tail := some tail} = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
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
    simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
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
  rw [runtime.compiler.code_region_loop,loop]
  simp only [runtime.compiler.code_region_loop.body]
  split <;> simp

private theorem compiler_split_body_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (allowed : id.val ≤ 10 ∨ id.val = 12) :
    runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) =
      .ok (if id = 10#u8 then .cont (last,true,pos,last)
        else .cont (last,false,Slice.len data,Slice.len data)) := by
  obtain ⟨middle,count,header,decoded,lastValue,bounded⟩ := h
  obtain ⟨position,byte,advance⟩ := header.byte.single
  have read := Itasca.reader.read_u32_leb.complete data middle count first decoded
  have post : runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) ⦃ result =>
      result = if id = 10#u8 then .cont (last,true,pos,last) else .cont (last,false,Slice.len data,Slice.len data) ⦄ := by
    unfold runtime.compiler.code_region_loop.body
    have inside : pos < Slice.len data := by scalar_tac
    simp only [inside,↓reduceIte,Bool.false_eq_true]
    step as ⟨opcode,lookup⟩
    have actual : opcode = id := by simpa only [lookup] using byte
    simp only [actual,byte]
    by_cases high : id > 10#u8
    · have countId : id = 12#u8 := UScalar.eq_of_val_eq (by scalar_tac)
      simp only [high,↓reduceIte,countId,bne_self_eq_false,Bool.false_eq_true]
      step as ⟨advanced,advancedValue⟩
      have same : advanced = middle := UScalar.eq_of_val_eq (by omega)
      subst advanced
      simp only [compiler_leb_eq,read,bind_ok,lift]
      step as ⟨remaining,remainingValue⟩
      step as ⟨finish,finishValue⟩
      have same : finish = last := UScalar.eq_of_val_eq (by scalar_tac)
      subst finish
      split <;> simp_all
    · simp only [high,↓reduceIte]
      step as ⟨advanced,advancedValue⟩
      have same : advanced = middle := UScalar.eq_of_val_eq (by omega)
      subst advanced
      simp only [compiler_leb_eq,read,bind_ok,lift]
      step as ⟨remaining,remainingValue⟩
      step as ⟨finish,finishValue⟩
      have same : finish = last := UScalar.eq_of_val_eq (by scalar_tac)
      subst finish
      split <;> simp_all
  obtain ⟨result,called,same⟩ := WP.spec_imp_exists post
  exact called.trans (congrArg Result.ok same)

private theorem compiler_split_loop_eof (data : Slice U8) :
    compilerScan data (Slice.len data) = .ok (Slice.len data,Slice.len data) := by
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  simp [runtime.compiler.code_region_loop.body]

private theorem compiler_split_skip_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (allowed : id.val < 10 ∨ id.val = 12) :
    compilerScan data pos = compilerScan data last := by
  have body := compiler_split_body_section data pos first last id h (by omega)
  have notCode : id ≠ 10#u8 := by scalar_tac
  simp only [notCode,↓reduceIte] at body
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  dsimp only
  rw [body]
  simp only [bind_ok]
  unfold compilerScan runtime.compiler.code_region_loop
  rfl

private theorem compiler_split_code_section (data : Slice U8) (pos first last : Usize)
    (h : SectionHeader data pos 10#u8 first last) : compilerScan data pos = .ok (pos,last) := by
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  dsimp only
  rw [compiler_split_body_section data pos first last 10#u8 h (by decide)]
  simp only [↓reduceIte,bind_ok]
  exact compiler_found data last pos last

private theorem compiler_split_after_code (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (high : 10 < id.val) (notCount : id.val ≠ 12) :
    compilerScan data pos = .ok (pos,pos) := by
  obtain ⟨_,_,header,_,_,_⟩ := h
  obtain ⟨position,byte,_⟩ := header.byte.single
  have post : runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) ⦃ result =>
      result = .cont (pos,true,pos,pos) ⦄ := by
    unfold runtime.compiler.code_region_loop.body
    have inside : pos < Slice.len data := by scalar_tac
    simp only [inside,↓reduceIte,Bool.false_eq_true]
    step as ⟨opcode,lookup⟩
    have actual : opcode = id := by simpa only [lookup] using byte
    simp only [actual,byte]
    have above : id > 10#u8 := by scalar_tac
    have different : id ≠ 12#u8 := by intro same; have value := congrArg UScalar.val same; scalar_tac
    simp [above,different]
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists post
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  dsimp only
  rw [called]
  simp only [bind_ok]
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
