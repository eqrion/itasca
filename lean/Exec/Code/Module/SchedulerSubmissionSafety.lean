import Exec.Code.Module.SchedulerSafety
import Exec.Code.Module.SubmitTotal
import Exec.Code.Module.CompileSubmit

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

theorem CompileEntryWitness.schedulerReady {A : Type} {ops : runtime.platform.Alloc A}
    {before after : CompileScheduler A} {worker finalWorker : stream.CodeBatch}
    (entry : CompileEntryWitness ops before after worker finalWorker)
    {env : module.Env} {cursor : Nat} (ready : SchedulerReady env cursor before) :
    SchedulerReady env cursor after := by
  rw [entry.published]
  refine ⟨ready.signatures,ready.functionSlots,?_,ready.origin,ready.queue,ready.cursorBound⟩
  simpa only [alloc.vec.Vec.set_val_eq,List.length_set] using ready.functions

/-- The queue's headroom follows the issued cursor, rather than a separate
allocator assumption. Entry termination is required only for this batch's
actual dispatch/validation successors. -/
theorem compiler_submit_safety {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (env : module.Env)
    (issued : StreamBatch.Issued) (sameEnv : issued.env = env) (bounded : issued.Bounded)
    (scheduler : CompileScheduler A) (ready : SchedulerReady env issued.first_func.val scheduler)
    (entries : ∀ current worker, SchedulerReady env issued.first_func.val current →
      StreamBatch.Reachable issued worker → CompileScheduler.compile_entry ops current worker ⦃ _ => True ⦄) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops scheduler issued.seed ⦃ out =>
      out.1 = .Ok () → SchedulerReady env (issued.first_func.val + issued.num_funcs.val) out.2 ⦄ := by
  let safe := fun (current : CompileScheduler A) (worker : stream.CodeBatch) => SchedulerReady env issued.first_func.val current ∧
    StreamBatch.Reachable issued worker
  have entrySafe : ∀ current worker, safe current worker →
      CompileScheduler.compile_entry ops current worker ⦃ out => out.1 = .Ok () → safe out.2.1 out.2.2 ⦄ := by
    intro current worker held
    obtain ⟨⟨status,after,batch⟩,run,_⟩ := WP.spec_imp_exists (entries current worker held.1 held.2)
    rw [run]
    apply (WP.spec_ok _).mpr
    intro accepted
    dsimp only at accepted
    obtain ⟨w⟩ := compile_entry_accepted ops current after worker batch (by simpa only [accepted] using run)
    exact ⟨w.schedulerReady held.1,w.reachable held.2⟩
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
    ready (fun _ _ _ _ held w => w.schedulerReady held)
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

end Itasca.Runtime.Code
