import Itasca.Runtime.Compiler.Module.CompileEntries
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- The eager submission loop requires entry termination only at reached
scheduler/worker pairs. An ordinary entry error immediately ends the loop. -/
theorem compiler_submit_loop_total_on {A : Type} (ops : runtime.platform.Alloc A)
    (safe : CompileScheduler A → stream.CodeBatch → Prop)
    (entries : ∀ scheduler worker, safe scheduler worker →
      CompileScheduler.compile_entry ops scheduler worker ⦃ out =>
        out.1 = .Ok () → safe out.2.1 out.2.2 ⦄)
    (scheduler : CompileScheduler A) (worker : stream.CodeBatch)
    (index : Usize) (status : core.result.Result Unit error.Error)
    (held : status = .Ok () → safe scheduler worker) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
      ops scheduler worker index status ⦃ out =>
        ∃ final batch result, out = submitPack final batch result ∧
          (result = .Ok () → safe final batch) ⦄ := by
  unfold CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
  apply loop.spec_decr_nat (fun st => Usize.max - st.2.2.1.val)
    (fun st => st.2.2.2 = .Ok () → safe st.1 st.2.1)
  · rintro ⟨scheduler,worker,index,status⟩ held
    simp only [CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,Itasca.stream.CodeBatch.len,bind_ok]
    split
    · rename_i inbounds
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok,bind_ok,Bool.false_eq_true,↓reduceIte,WP.spec_ok]
        exact ⟨scheduler,worker,.Err error,rfl,by intro h; cases h⟩
      | Ok result =>
        cases result
        simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
        obtain ⟨⟨result,next,batch⟩,run,preserved⟩ := WP.spec_imp_exists (entries scheduler worker (held rfl))
        rw [run]
        simp only [bind_ok]
        step
        exact ⟨preserved,by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨scheduler,worker,status,rfl,held⟩
  · exact held

/-- Queue publication is safe once reached entry states provide bounded queue
headroom. The successful entry invariant is not required after a rejection. -/
theorem compiler_submit_total_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (safe : CompileScheduler A → stream.CodeBatch → Prop)
    (entries : ∀ scheduler worker, safe scheduler worker →
      CompileScheduler.compile_entry ops scheduler worker ⦃ out =>
        out.1 = .Ok () → safe out.2.1 out.2.2 ⦄)
    (room : ∀ scheduler worker, safe scheduler worker → scheduler.completed.val.length < Usize.max)
    (scheduler : CompileScheduler A) (worker : stream.CodeBatch)
    (held : safe scheduler worker) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops scheduler worker
      ⦃ _ => True ⦄ := by
  obtain ⟨out,run,final,batch,result,rfl,preserved⟩ := WP.spec_imp_exists
    (compiler_submit_loop_total_on ops safe entries scheduler worker 0#usize (.Ok ()) (fun _ => held))
  unfold CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
  rw [run]
  simp only [submitPack,bind_ok,uncurry_apply_pair]
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok accepted =>
    cases accepted
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    obtain ⟨⟨result,budget,queue⟩,pushed,_⟩ := WP.spec_imp_exists
      (budget_push ops law final.budget final.completed batch (room final batch (preserved rfl)))
    rw [pushed]
    cases result <;> simp [visitor_result,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Compiler
