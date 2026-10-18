import Exec.Code.Module.SchedulerFunctions
namespace Exec.Code
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

/-- An actual batch run preserves the per-index ledger once its actual entry
witnesses have been certified. Reachability and fixed metadata are supplied to
the entry proof, rather than assumed again for each arbitrary worker. -/
theorem CompileEntries.functions {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    {env : module.Env} {sources : List funccode} {issued : StreamBatch.Issued}
    (reachable : StreamBatch.Reachable issued batch)
    (initial : PartialModuleFunctions env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ DefinedFunctionCode env typeIndex source w.final.function) :
    PartialModuleFunctions env sources after.functions.val := by
  have result := run.fold
    (fun scheduler worker => schedulerStatic scheduler = schedulerStatic before ∧
      StreamBatch.Reachable issued worker ∧ PartialModuleFunctions env sources scheduler.functions.val)
    ⟨rfl, reachable, initial⟩ ?_
  · exact result.2.2
  · intro current worker next nextWorker invariant w
    obtain ⟨typeIndex, source, lookup, sourceLookup, code⟩ := entries current next worker nextWorker invariant.1 invariant.2.1 w
    exact ⟨w.static.trans invariant.1, w.reachable invariant.2.1,
      w.functions invariant.2.2 typeIndex source lookup sourceLookup code⟩

/-- Submission's queue push changes no function slot. The ledger after a
successful real batch therefore contains every previously checked entry and
each newly certified entry at its issued index. -/
theorem compiler_submit_functions {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before after : runtime.compiler.CompileScheduler A)
    (issued : StreamBatch.Issued) (env : module.Env) (sources : List funccode)
    (initial : PartialModuleFunctions env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ DefinedFunctionCode env typeIndex source w.final.function)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before issued.seed = .ok (.Ok (), after)) :
    PartialModuleFunctions env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  obtain ⟨middle, worker, run, queue, same⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
  have certificates := run.functions .seed initial entries
  rw [same]
  exact ⟨certificates, run.static⟩

theorem compiler_poll_functions {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    {env : module.Env} {sources : List funccode} (initial : PartialModuleFunctions env sources before.functions.val)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    PartialModuleFunctions env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  rw [(compiler_poll_accepted allocator before after batch accepted).2]
  exact ⟨initial, rfl⟩
end Exec.Code
