import Itasca.Runtime.Compiler.Module.FinishTotal
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEntry
import Itasca.Runtime.Compiler.Module.SchedulerSafety
import Itasca.Stream.BatchBounds

namespace Itasca.Runtime.Code
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
  obtain ⟨_,_,_,_,_,first,count,_⟩ := identity
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
    obtain ⟨_,_,_,code,offset,_,_,_⟩ := identity
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

end Itasca.Runtime.Code
