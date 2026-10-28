import Itasca.Runtime.Code.Module.SchedulerSubmission
import Itasca.Runtime.Code.Module.SchedulerCapacities
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- An actual batch run preserves the per-index ledger once its actual entry
witnesses have been certified. Reachability and fixed metadata are supplied to
the entry proof, rather than assumed again for each arbitrary worker. -/
theorem CompileEntries.capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    {profile : ValidationProfile} {env : module.Env} {sources : List funccode} {issued : StreamBatch.Issued}
    (reachable : StreamBatch.Reachable issued batch)
    (initial : PartialModuleCapacities profile env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ FunctionCapacity profile env typeIndex source w.final.function) :
    PartialModuleCapacities profile env sources after.functions.val := by
  have result := run.fold
    (fun scheduler worker => schedulerStatic scheduler = schedulerStatic before ∧
      StreamBatch.Reachable issued worker ∧ PartialModuleCapacities profile env sources scheduler.functions.val)
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
    (issued : StreamBatch.Issued) (profile : ValidationProfile) (env : module.Env) (sources : List funccode)
    (initial : PartialModuleCapacities profile env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ FunctionCapacity profile env typeIndex source w.final.function)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before issued.seed = .ok (.Ok (), after)) :
    PartialModuleCapacities profile env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  obtain ⟨middle, worker, run, queue, same⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
  have certificates := run.capacities .seed initial entries
  rw [same]
  exact ⟨certificates, run.static⟩

theorem compiler_poll_capacities {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    {profile : ValidationProfile} {env : module.Env} {sources : List funccode} (initial : PartialModuleCapacities profile env sources before.functions.val)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    PartialModuleCapacities profile env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  rw [(compiler_poll_accepted allocator before after batch accepted).2]
  exact ⟨initial, rfl⟩
end Itasca.Runtime.Code
