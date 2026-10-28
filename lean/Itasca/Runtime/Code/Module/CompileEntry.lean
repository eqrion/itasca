import Itasca.Runtime.Code.Local.Relations.Common.EntryTypedSteps
import Itasca.Runtime.Code.Local.Callbacks.Common.Finish
import Itasca.Runtime.Code.Local.Relations.Common.FunctionEntry
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

/-- The successful scheduler entry consists of an actual batch dispatch,
compiler construction, validation, finish, and insertion at the source index. -/
structure CompileEntryWitness {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A)
    (batch finalBatch : stream.CodeBatch) where
  entry : stream.CodeEntry
  dispatched : stream.CodeBatch
  batchStart : Usize
  initial : runtime.compiler.FunctionCompiler A
  final : runtime.compiler.FunctionCompiler A
  dispatch : stream.CodeBatch.next_entry batch = .ok (.Ok entry, dispatched)
  coordinates : (before.code_start + dispatched.code_offset : Result Usize) = .ok batchStart
  created : runtime.compiler.FunctionCompiler.new allocator
    (alloc.vec.Vec.deref before.signatures) (alloc.vec.Vec.deref before.func_param_slots)
    {before.budget with marker := ()} batchStart = .ok initial
  validated : stream.CodeBatch.validate_func
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator)
    dispatched entry.index initial = .ok (.Ok (), finalBatch, final)
  finished : runtime.compiler.FunctionCompiler.finish allocator final (.Ok ()) =
    .ok (.Ok final.function, final.budget)
  indexBound : entry.index.val < before.functions.val.length
  vacant : before.functions.val[entry.index.val]? = some none
  published : after = {before with functions := before.functions.set entry.index (some final.function), budget := final.budget}

theorem compile_entry_accepted {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch finalBatch : stream.CodeBatch)
    (accepted : runtime.compiler.CompileScheduler.compile_entry allocator before batch =
      .ok (.Ok (), after, finalBatch)) :
    Nonempty (CompileEntryWitness allocator before after batch finalBatch) := by
  unfold runtime.compiler.CompileScheduler.compile_entry at accepted
  obtain ⟨⟨dispatchResult, dispatched⟩, dispatch, tail⟩ := bind_ok_inv _ _ _ accepted
  cases dispatchResult with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
  | Ok entry =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      runtime.compiler.Budget.copy_state, Itasca.stream.CodeBatch.impl.code_offset, uncurry_apply_pair] at tail
    obtain ⟨batchStart, coordinates, tail⟩ := bind_ok_inv _ _ _ tail
    obtain ⟨initial, created, tail⟩ := bind_ok_inv _ _ _ tail
    obtain ⟨⟨validationResult, checkedBatch, final⟩, validated, tail⟩ := bind_ok_inv _ _ _ tail
    obtain ⟨⟨finishResult, budget⟩, finished, tail⟩ := bind_ok_inv _ _ _ tail
    cases finishResult with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok function =>
      obtain ⟨rfl, rfl, rfl, closed, wellFormed⟩ :=
        compiler_finish_accepted allocator final validationResult function budget finished
      simp only [uncurry_apply_pair, bind_ok] at tail
      split at tail
      · simp at tail
      · rename_i fits
        have bound : entry.index.val < before.functions.val.length := by scalar_tac
        obtain ⟨value, lookup, tail⟩ := bind_ok_inv _ _ _ tail
        have lookupSpec := alloc.vec.Vec.index_usize_spec before.functions entry.index bound
        rw [alloc.vec.Vec.index_slice_index] at lookup
        rw [lookup, WP.spec_ok] at lookupSpec
        cases value with
        | some existing => simp [core.option.Option.is_some] at tail
        | none =>
          simp only [core.option.Option.is_some] at tail
          obtain ⟨⟨old, back⟩, mutable, tail⟩ := bind_ok_inv _ _ _ tail
          have mutableSpec := alloc.vec.Vec.index_mut_usize_spec before.functions entry.index bound
          rw [alloc.vec.Vec.index_mut_slice_index] at mutable
          rw [mutable, WP.spec_ok] at mutableSpec
          obtain ⟨oldEq, backEq⟩ := mutableSpec
          simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨_, schedulerEq, batchEq⟩ := tail
          subst finalBatch
          refine ⟨⟨entry, dispatched, batchStart, initial, final, dispatch, coordinates, created,
            validated, finished, bound, ?_, ?_⟩⟩
          · rw [List.getElem?_eq_getElem bound, ← lookupSpec]
          · simpa only [backEq] using schedulerEq.symm

theorem CompileEntryWitness.reachable {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch) :
    StreamBatch.Reachable issued finalBatch :=
  .validate _ (.dispatch reachable w.dispatch) w.validated

theorem CompileEntryWitness.metadata {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch) :
    w.dispatched.env = batch.env ∧ w.dispatched.profile = batch.profile ∧
      w.dispatched.num_validated = batch.num_validated ∧
      w.dispatched.first_func = batch.first_func ∧
      after.completed = before.completed ∧ after.signatures = before.signatures ∧
      after.func_param_slots = before.func_param_slots ∧ after.tail = before.tail ∧
      after.code_start = before.code_start := by
  simp only [w.published]
  rcases stream.CodeBatch.next_entry.cases batch w.dispatched (.Ok w.entry) w.dispatch with same | changed
  · simp [same]
  · obtain ⟨_, _, _, _, _, _, _, _, same⟩ := changed
    simp [same]

theorem CompileEntryWitness.typed {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
    (bounds : CodeEntry.Bounds batch.env) :
    ∃ finish, w.entry.index.val = batch.first_func.val + batch.num_validated.val ∧
      ∃ entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator)
          w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
          w.initial w.final w.dispatched.profile,
        TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator)
          entry.body w.dispatched.env entry.ctx entry.typeIdx (Wasm2.initial entry.typeIdx) entry.startedState
          w.final := by
  obtain ⟨finish, index, entry, typed⟩ := batch_typed_steps _ w.dispatched finalBatch w.entry.index
    w.initial w.final (by simpa only [w.metadata.1] using bounds) w.validated
  exact ⟨finish, by simpa only [w.metadata.2.2.1, w.metadata.2.2.2.1] using index, entry, typed⟩
end Itasca.Runtime.Code
