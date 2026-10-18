import Exec.Code.Module.CompileEntry
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

/-- The actual successful per-function scheduler calls in one submitted batch. -/
inductive CompileEntries {A : Type} (allocator : runtime.platform.Alloc A) :
    runtime.compiler.CompileScheduler A → stream.CodeBatch →
      runtime.compiler.CompileScheduler A → stream.CodeBatch → Prop where
  | nil (scheduler batch) : CompileEntries allocator scheduler batch scheduler batch
  | next {before batch middle nextBatch after finalBatch}
      (entry : runtime.compiler.CompileScheduler.compile_entry allocator before batch = .ok (.Ok (), middle, nextBatch))
      (rest : CompileEntries allocator middle nextBatch after finalBatch) :
      CompileEntries allocator before batch after finalBatch

def submitPack {A : Type} (scheduler : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    (result : core.result.Result Unit error.Error) :=
  (scheduler.signatures, scheduler.func_param_slots, scheduler.completed, scheduler.functions,
    scheduler.tail, scheduler.code_start, scheduler.budget, batch.module_id, batch.batch_id,
    batch.profile, batch.env, batch.code, batch.code_offset, batch.first_func, batch.num_funcs,
    batch.num_dispatched, batch.dispatch_end, batch.num_validated, batch.validated_end, batch.error, result)

theorem submitPack_injective {A : Type} (left right : runtime.compiler.CompileScheduler A)
    (batch other : stream.CodeBatch) (result final : core.result.Result Unit error.Error)
    (same : submitPack left batch result = submitPack right other final) :
    left = right ∧ batch = other ∧ result = final := by
  cases left
  cases right
  cases batch
  cases other
  simp_all [submitPack]

/-- Any successful returned submission loop consists entirely of actual
successful entry compilations, with exact batch/visitor state succession. -/
theorem submit_loop_accepted {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch finalBatch : stream.CodeBatch)
    (index : Usize) (result : core.result.Result Unit error.Error)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
      allocator before batch index result = .ok (submitPack after finalBatch (.Ok ()))) :
    result = .Ok () ∧ CompileEntries allocator before batch after finalBatch := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before batch index result with
  | h n ih =>
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
      Exec.stream.CodeBatch.len, Itasca.stream.CodeBatch.len, bind_ok] at accepted
    split at accepted
    · cases result with
      | Err error => simp [core.result.Result.is_ok, submitPack] at accepted
      | Ok acceptedUnit =>
        cases acceptedUnit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨nextResult, middle, nextBatch⟩, entry, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
            allocator middle nextBatch nextIndex nextResult = .ok (submitPack after finalBatch (.Ok ())) := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop,
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
            Exec.stream.CodeBatch.len, Itasca.stream.CodeBatch.len, core.result.Result.is_ok] using tail
        obtain ⟨success, rest⟩ := ih _ smaller middle nextBatch nextIndex nextResult tail' rfl
        subst nextResult
        exact ⟨rfl, .next entry rest⟩
    · have packed : submitPack before batch result = submitPack after finalBatch (.Ok ()) := by
        simpa only [submitPack, bind_ok, Result.ok.injEq] using accepted
      obtain ⟨rfl, rfl, rfl⟩ := submitPack_injective _ _ _ _ _ _ packed
      exact ⟨rfl, .nil _ _⟩

theorem CompileEntries.reachable {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch) :
    StreamBatch.Reachable issued finalBatch := by
  induction run with
  | nil => exact reachable
  | next entry rest ih =>
    obtain ⟨w⟩ := compile_entry_accepted _ _ _ _ _ entry
    exact ih (w.reachable reachable)

theorem CompileEntries.completed {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch) : after.completed = before.completed := by
  induction run with
  | nil => rfl
  | next entry rest ih =>
    obtain ⟨w⟩ := compile_entry_accepted _ _ _ _ _ entry
    exact ih.trans w.metadata.2.2.2.2.1

/-- Fold retained compiler certificates through the exact successful scheduler
calls. The step obligation receives the concrete entry witness. -/
theorem CompileEntries.fold {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    (invariant : runtime.compiler.CompileScheduler A → stream.CodeBatch → Prop)
    (initial : invariant before batch)
    (preserved : ∀ before batch after finalBatch,
      invariant before batch → CompileEntryWitness allocator before after batch finalBatch →
      invariant after finalBatch) : invariant after finalBatch := by
  induction run with
  | nil => exact initial
  | next entry rest ih =>
    obtain ⟨w⟩ := compile_entry_accepted _ _ _ _ _ entry
    exact ih (preserved _ _ _ _ initial w)
end Exec.Code
