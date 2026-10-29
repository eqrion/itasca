import Itasca.Runtime.Compiler.Module.CompileEntries
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpression
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

/-- Successful submission compiles the actual batch and appends precisely its
resulting worker to the completed queue. No synthetic worker is introduced. -/
theorem compiler_submit_accepted {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (before after : runtime.compiler.CompileScheduler A)
    (batch : stream.CodeBatch)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before batch = .ok (.Ok (), after)) :
    ∃ middle worker, CompileEntries allocator before batch middle worker ∧
      after.completed.val = before.completed.val ++ [worker] ∧
      after = {middle with completed := after.completed, budget := after.budget} := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch at accepted
  obtain ⟨⟨signatures, slots, completed, functions, tail, codeStart, budget,
    moduleId, batchId, profile, env, code, offset, first, count, dispatched, dispatchEnd,
    validated, validatedEnd, error, result⟩, loopRun, rest⟩ := bind_ok_inv _ _ _ accepted
  let middle : runtime.compiler.CompileScheduler A :=
    {signatures, func_param_slots := slots, completed, functions, tail, code_start := codeStart, budget}
  let worker : stream.CodeBatch :=
    {module_id := moduleId, batch_id := batchId, profile, env, code, code_offset := offset,
      first_func := first, num_funcs := count, num_dispatched := dispatched, dispatch_end := dispatchEnd,
      num_validated := validated, validated_end := validatedEnd, error}
  simp only [uncurry_apply_pair] at rest
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok acceptedUnit =>
    cases acceptedUnit
    have packed : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
        allocator before batch 0#usize (.Ok ()) = .ok (submitPack middle worker (.Ok ())) := loopRun
    have run := (submit_loop_accepted allocator before middle batch worker 0#usize (.Ok ()) packed).2
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, finalBudget, queue⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => simp [runtime.compiler.visitor_result, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok acceptedUnit =>
      cases acceptedUnit
      simp only [uncurry_apply_pair, runtime.compiler.visitor_result,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      obtain ⟨_, appended⟩ := budget_push_success allocator law budget finalBudget completed queue worker pushed
      refine ⟨middle, worker, run, ?_, rfl⟩
      change queue.val = before.completed.val ++ [worker]
      rw [appended]
      exact congrArg (fun queue => queue.val ++ [worker]) run.completed

/-- A successful poll removes an actual queued worker and preserves the rest
of the scheduler, including all retained function certificates. -/
theorem compiler_poll_accepted {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    before.completed.val = after.completed.val ++ [batch] ∧
      after = {before with completed := after.completed} := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch at accepted
  simp only [alloc.vec.Vec.pop, bind_ok] at accepted
  cases empty : before.completed.val.getLast? with
  | none => simp [empty, core.option.Option.ok_or] at accepted
  | some value =>
    simp [empty, core.option.Option.ok_or] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    constructor
    · simpa using (List.dropLast_append_getLast? value empty).symm
    · rfl
end Itasca.Runtime.Code
