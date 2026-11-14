import Itasca.Runtime.Compiler.Module.CodeRegionContracts
import Itasca.Stream.Header
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FinishContracts
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedTotal
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.FunsCompiler
import Itasca.Stream.Source
import Itasca.Binary.Leb128
import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Relations.Instructions.InstructionCheckAcceptance
import Itasca.Runtime.Compiler.Local.Relations.Function.EntryTypedSteps
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend

/-!
Sections, each formerly its own module: Stream, CodeRegion, WellFormedTotal, FinishTotal, CompileEntry, CompileEntries, CompileSubmit.
-/

/-! ## Stream -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open runtime.compiler

/-- Region offsets come from the module scanner; they are ordered positions in
one immutable byte slice. -/
def SourceBounds (source : CompileSource) : Prop :=
  source.code_start.val ≤ source.code_end.val ∧ source.code_end.val ≤ source.bytes.length

def sourceEnvironment (source : CompileSource) := source.bytes.val.take source.code_start.val

def sourceCode (source : CompileSource) :=
  source.bytes.val.slice source.code_start.val source.code_end.val

def sourceTail (source : CompileSource) := source.bytes.val.drop source.code_end.val

@[step] theorem source_environment_spec (source : CompileSource) (h : SourceBounds source) :
    CompileSource.Insts.ItascaStreamSource.environment source ⦃ r =>
      ∃ bytes, r = .Ok bytes ∧ bytes.val = sourceEnvironment source ⦄ := by
  unfold runtime.compiler.CompileSource.Insts.ItascaStreamSource.environment
  simp only [SourceBounds] at h
  step*
  simp_all [sourceEnvironment]

@[step] theorem source_tail_spec (source : CompileSource) (h : SourceBounds source) :
    CompileSource.Insts.ItascaStreamSource.tail source ⦃ r =>
      ∃ bytes, r = .Ok bytes ∧ bytes.val = sourceTail source ⦄ := by
  unfold runtime.compiler.CompileSource.Insts.ItascaStreamSource.tail
  simp only [SourceBounds] at h
  step*
  simp_all [sourceTail]

@[step] theorem source_code_len_spec (source : CompileSource) (h : SourceBounds source) :
    CompileSource.Insts.ItascaStreamSource.code_len source ⦃ n =>
      n.val = source.code_end.val - source.code_start.val ⦄ := by
  unfold runtime.compiler.CompileSource.Insts.ItascaStreamSource.code_len
  simp only [SourceBounds] at h
  step*

@[step] theorem source_code_spec (source : CompileSource) (h : SourceBounds source)
    (first last : Usize) :
    CompileSource.Insts.ItascaStreamSource.code source first last ⦃ r => match r with
      | .Ok bytes => first.val ≤ last.val ∧ last.val ≤ (sourceCode source).length ∧
          bytes.val = (sourceCode source).slice first.val last.val
      | .Err e => e = .Host ∧
          (last.val < first.val ∨ (sourceCode source).length < last.val) ⦄ := by
  have hc : (sourceCode source).length = source.code_end.val - source.code_start.val := by
    simp only [sourceCode, List.slice_length]
    have := h.2
    change source.code_end.val ≤ source.bytes.val.length at this
    omega
  unfold runtime.compiler.CompileSource.Insts.ItascaStreamSource.code
  step*
  refine ⟨by scalar_tac, by scalar_tac, ?_⟩
  have hl : last.val - first.val ≤ (source.code_end.val - source.code_start.val) - first.val := by
    scalar_tac
  simp only [s_post, i1_post, i2_post, sourceCode, List.slice, List.drop_take,
    List.drop_drop, List.take_take]
  congr 1; omega


theorem source_code_length (source : CompileSource) (h : SourceBounds source) :
    (sourceCode source).length = source.code_end.val - source.code_start.val := by
  simp only [sourceCode, List.slice_length]
  have := h.2
  change source.code_end.val ≤ source.bytes.val.length at this
  omega

/-- These views reconstruct the same complete module bytes. -/
theorem source_recombine (source : CompileSource) (h : SourceBounds source) :
    sourceEnvironment source ++ sourceCode source ++ sourceTail source = source.bytes.val := by
  unfold sourceEnvironment sourceCode sourceTail List.slice
  rw [← List.take_add, Nat.add_sub_of_le h.1, List.take_append_drop]

theorem source_coherent (source : CompileSource) (h : SourceBounds source) :
    Itasca.StreamSource.Coherent CompileSource.Insts.ItascaStreamSource source
      (sourceEnvironment source) (sourceCode source) (sourceTail source) := by
  constructor
  · intro bytes hr
    have hs := source_environment_spec source h
    change runtime.compiler.CompileSource.Insts.ItascaStreamSource.environment source = _ at hr
    simp only [hr, WP.spec_ok] at hs
    obtain ⟨other, heq, hb⟩ := hs
    cases heq
    exact hb
  · intro len hr
    have hs := source_code_len_spec source h
    change runtime.compiler.CompileSource.Insts.ItascaStreamSource.code_len source = _ at hr
    simpa only [hr, WP.spec_ok, source_code_length source h] using hs
  · intro first last bytes _ _ hr
    have hs := source_code_spec source h first last
    change runtime.compiler.CompileSource.Insts.ItascaStreamSource.code source first last = _ at hr
    simp only [hr, WP.spec_ok] at hs
    exact hs.2.2
  · intro bytes hr
    have hs := source_tail_spec source h
    change runtime.compiler.CompileSource.Insts.ItascaStreamSource.tail source = _ at hr
    simp only [hr, WP.spec_ok] at hs
    obtain ⟨other, heq, hb⟩ := hs
    cases heq
    exact hb

theorem source_available (source : CompileSource) (h : SourceBounds source) :
    Itasca.StreamSource.Available CompileSource.Insts.ItascaStreamSource source
      (sourceEnvironment source) (sourceCode source) (sourceTail source) := by
  constructor
  · obtain ⟨_, hr, bytes, rfl, hb⟩ := WP.spec_imp_exists (source_environment_spec source h)
    exact ⟨bytes, hr, hb⟩
  · obtain ⟨len, hr, hb⟩ := WP.spec_imp_exists (source_code_len_spec source h)
    exact ⟨len, hr, by simpa only [source_code_length source h] using hb⟩
  · intro first last horder hbound
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (source_code_spec source h first last)
    cases r with
    | Ok bytes => exact ⟨bytes, hr, hp.2.2⟩
    | Err e => simp only at hp; omega
  · obtain ⟨_, hr, bytes, rfl, hb⟩ := WP.spec_imp_exists (source_tail_spec source h)
    exact ⟨bytes, hr, hb⟩

/-- Invalid read ranges return an ordinary source error; valid bounds suffice
for every callback to return without a modeled panic or divergence. -/
theorem source_callbacks_total (source : CompileSource) (h : SourceBounds source) :
    Itasca.StreamSource.CallbacksTotal CompileSource.Insts.ItascaStreamSource source := by
  constructor
  · obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_environment_spec source h)
    exact ⟨r, hr⟩
  · obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_code_len_spec source h)
    exact ⟨r, hr⟩
  · intro first last
    obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_code_spec source h first last)
    exact ⟨r, hr⟩
  · obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (source_tail_spec source h)
    exact ⟨r, hr⟩

end Itasca.Runtime.Compiler

end

/-! ## CodeRegion -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem code_region_body_spec (bytes : Slice U8) (pos : Usize) (found : Bool)
    (first last : Usize) (ordered : first.val ≤ last.val) (bounded : last.val ≤ bytes.length) :
    runtime.compiler.code_region_loop.body bytes pos found first last ⦃ out => match out with
      | .done (start, finish) => start.val ≤ finish.val ∧ finish.val ≤ bytes.length
      | .cont (next, seen, start, finish) => start.val ≤ finish.val ∧ finish.val ≤ bytes.length ∧
          regionMeasure bytes next seen < regionMeasure bytes pos found ⦄ := by
  exact runtime.compiler.code_region_loop.body.total bytes pos found first last ordered bounded

/-- Code-region scanning always returns ordered in-bounds source views,
including malformed and truncated modules. -/
@[step] theorem code_region_spec (bytes : Slice U8) :
    runtime.compiler.code_region bytes ⦃ result => result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  exact runtime.compiler.code_region.total bytes

end Itasca.Runtime.Compiler

end

/-! ## FinishTotal -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Finishing a compiler returns normally for arbitrary internal records and
validation results. Invalid frames or bytecode are rejected by the actual gate. -/
@[step] theorem compiler_finish_total {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (validated : core.result.Result Unit Itasca.error.Error) :
    runtime.compiler.FunctionCompiler.finish ops compiler validated ⦃ out => out.2 = compiler.budget ⦄ := by
  exact runtime.compiler.FunctionCompiler.finish.total ops compiler validated
end Itasca.Runtime.Compiler

end

/-! ## CompileEntry -/

section

/-!
Compilation-entry bounds and its retained certificate, used by the module scheduler construction.
-/

/-! ## Compile Entry -/

section

namespace Itasca.Runtime.Compiler
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

/-- The recorded dispatch, validation, finish and vacant-slot stages replay the
actual successful scheduler call. -/
theorem CompileEntryWitness.called {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch) :
    runtime.compiler.CompileScheduler.compile_entry ops before batch = .ok (.Ok (), after, finalBatch) := by
  rw [w.published]
  unfold runtime.compiler.CompileScheduler.compile_entry
  simp only [w.dispatch, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
    runtime.compiler.Budget.copy_state, Itasca.stream.CodeBatch.impl.code_offset,
    uncurry_apply_pair, w.coordinates, w.created, w.validated, w.finished]
  have fits : ¬ w.entry.index ≥ alloc.vec.Vec.len before.functions := by
    have := w.indexBound
    scalar_tac
  simp only [fits, ↓reduceIte]
  have slotBound := w.indexBound
  have found := alloc.vec.Vec.index_usize_spec before.functions w.entry.index w.indexBound
  have missing : before.functions.val[w.entry.index.val] = none := by
    simpa only [List.getElem?_eq_getElem w.indexBound, Option.some.injEq] using w.vacant
  simp only [missing] at found
  obtain ⟨existing, lookup, same⟩ := WP.spec_imp_exists found
  subst existing
  simp only [alloc.vec.Vec.index_slice_index]
  rw [lookup]
  simp only [bind_ok, core.option.Option.is_some, ↓reduceIte]
  obtain ⟨⟨old, back⟩, mutable, oldEq, backEq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec before.functions w.entry.index w.indexBound)
  simp only [alloc.vec.Vec.index_mut_slice_index]
  rw [mutable]
  simp only [bind_ok, uncurry_apply_pair, backEq]
  rfl

theorem CompileEntryWitness.reachable {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch) :
    StreamBatch.Reachable issued finalBatch :=
  .validate _ (.dispatch reachable w.dispatch) w.validated

theorem CompileEntryWitness.metadata {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness allocator before after batch finalBatch) :
    w.dispatched.env = batch.env ∧
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
          w.initial w.final,
        TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator)
          entry.body w.dispatched.env entry.ctx entry.typeIdx (Wasm2.initial entry.typeIdx) entry.startedState
          w.final := by
  obtain ⟨finish, index, entry, typed⟩ := batch_typed_steps _ w.dispatched finalBatch w.entry.index
    w.initial w.final (by simpa only [w.metadata.1] using bounds) w.validated
  exact ⟨finish, by simpa only [w.metadata.2.1, w.metadata.2.2.1] using index, entry, typed⟩
end Itasca.Runtime.Compiler

end

/-! ## Compile Entry Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The driver's issued byte cap and the scanned code origin bound all
absolute positions in an actually dispatched compiler batch. -/
theorem CompileEntryWitness.coordinate_bound {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val) :
    w.batchStart.val + w.dispatched.code.length ≤ Usize.max := by
  have identity := (StreamBatch.Reachable.dispatch reachable w.dispatch).validation.1
  obtain ⟨_, _, _, code, offset, _, _⟩ := identity
  have arithmetic := UScalar.add_equiv before.code_start w.dispatched.code_offset
  rw [w.coordinates] at arithmetic
  have position := arithmetic.2.1
  have cap : limits.MAX_MODULE_BYTES.val + limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
    simp only [limits.MAX_MODULE_BYTES]
    scalar_tac
  have size := bounded.2.2
  rw [code, offset] at *
  omega

/-- The successful entry's exact body span discharges the function-start
absolute-end premise; it need not be assumed independently by compilation. -/
theorem CompileEntryWitness.end_fits {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    {finish : Usize}
    (entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
      w.initial w.final) :
    w.batchStart.val + finish.val ≤ Usize.max := by
  have bound := w.coordinate_bound reachable bounded origin
  have span := entry.body_bytes.bound
  omega
end Itasca.Runtime.Compiler

end

end

/-! ## CompileEntries -/

section

namespace Itasca.Runtime.Compiler
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
    batch.env, batch.code, batch.code_offset, batch.first_func, batch.num_funcs,
    batch.num_dispatched, batch.dispatch_end, batch.num_validated, batch.validated_end, batch.error, result)

theorem submit_pack_injective {A : Type} (left right : runtime.compiler.CompileScheduler A)
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
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body, Itasca.stream.CodeBatch.len, bind_ok] at accepted
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
            runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body, Itasca.stream.CodeBatch.len, core.result.Result.is_ok] using tail
        obtain ⟨success, rest⟩ := ih _ smaller middle nextBatch nextIndex nextResult tail' rfl
        subst nextResult
        exact ⟨rfl, .next entry rest⟩
    · have packed : submitPack before batch result = submitPack after finalBatch (.Ok ()) := by
        simpa only [submitPack, bind_ok, Result.ok.injEq] using accepted
      obtain ⟨rfl, rfl, rfl⟩ := submit_pack_injective _ _ _ _ _ _ packed
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
    exact ih.trans w.metadata.2.2.2.1

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
end Itasca.Runtime.Compiler

end

/-! ## CompileSubmit -/

section

namespace Itasca.Runtime.Compiler
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
    moduleId, batchId, env, code, offset, first, count, dispatched, dispatchEnd,
    validated, validatedEnd, error, result⟩, loopRun, rest⟩ := bind_ok_inv _ _ _ accepted
  let middle : runtime.compiler.CompileScheduler A :=
    {signatures, func_param_slots := slots, completed, functions, tail, code_start := codeStart, budget}
  let worker : stream.CodeBatch :=
    {module_id := moduleId, batch_id := batchId, env, code, code_offset := offset,
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
    | Err error => simp [runtime.compiler.visitor_result.eq, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok acceptedUnit =>
      cases acceptedUnit
      simp only [uncurry_apply_pair, runtime.compiler.visitor_result.eq,
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
  rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch.eq] at accepted
  simp only [alloc.vec.Vec.pop, bind_ok] at accepted
  cases empty : before.completed.val.getLast? with
  | none => simp [empty, core.option.Option.ok_or] at accepted
  | some value =>
    simp [empty, core.option.Option.ok_or] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    constructor
    · simpa using (List.dropLast_append_getLast? value empty).symm
    · rfl
end Itasca.Runtime.Compiler

end

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca runtime.compiler

/-- Dispatch, compiler construction, final bytecode checking, and indexed
publication return normally. The remaining body obligation names only the
fresh compiler reached by this actual issued entry. -/
theorem _root_.Itasca.runtime.compiler.CompileScheduler.compile_entry.total {A : Type} (ops : runtime.platform.Alloc A)
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
  unfold runtime.compiler.CompileScheduler.compile_entry
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
      uncurry_apply_pair, runtime.compiler.Budget.copy_state,Itasca.stream.CodeBatch.impl.code_offset]
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

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca runtime.compiler

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.total {A : Type} (ops : runtime.platform.Alloc A)
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
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
  apply loop.spec_decr_nat (fun st => Usize.max - st.2.2.1.val)
    (fun st => st.2.2.2 = .Ok () → safe st.1 st.2.1)
  · rintro ⟨scheduler,worker,index,status⟩ held
    simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,Itasca.stream.CodeBatch.len,bind_ok]
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


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch.total {A : Type} (ops : runtime.platform.Alloc A)
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
    (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.total ops safe entries scheduler worker 0#usize (.Ok ()) (fun _ => held))
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
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
    cases result <;> simp [runtime.compiler.visitor_result.eq,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.done
    {A : Type} (ops : runtime.platform.Alloc A) (before : CompileScheduler A) (batch : stream.CodeBatch)
    (index : Usize) (ended : ¬ index < batch.num_funcs) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop ops before batch index (.Ok ()) =
      .ok (submitPack before batch (.Ok ())) := by
  rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop, loop]
  simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
    stream.CodeBatch.len, ended, ite_false, bind_ok, submitPack]

/-- A live submission step records the exact compiled worker and increment. -/
structure SubmitStep {A : Type} (ops : runtime.platform.Alloc A)
    (before : CompileScheduler A) (batch : stream.CodeBatch) (index : Usize) where
  middle : CompileScheduler A
  worker : stream.CodeBatch
  nextIndex : Usize
  more : index < batch.num_funcs
  compiled : CompileScheduler.compile_entry ops before batch = .ok (.Ok (), middle, worker)
  increment : (index + 1#usize : Result Usize) = .ok nextIndex

theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.available_step
    {A : Type} {ops : runtime.platform.Alloc A} {before : CompileScheduler A} {batch : stream.CodeBatch} {index : Usize}
    (step : SubmitStep ops before batch index) (after : CompileScheduler A) (worker : stream.CodeBatch)
    (continued : CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
      ops step.middle step.worker step.nextIndex (.Ok ()) = .ok (submitPack after worker (.Ok ()))) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop ops before batch index (.Ok ()) =
      .ok (submitPack after worker (.Ok ())) := by
  rw [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop, loop]
  simp only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
    stream.CodeBatch.len, bind_ok, step.more, ite_true, core.result.Result.is_ok, step.compiled,
    uncurry_apply_pair, step.increment]
  simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop,
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop.body,
    stream.CodeBatch.len, bind_ok, core.result.Result.is_ok] using continued

/-- Submission publishes the actual completed worker and exact allocated queue. -/
theorem _root_.Itasca.runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch.available
    {A : Type} (ops : runtime.platform.Alloc A) (before middle : CompileScheduler A)
    (batch worker : stream.CodeBatch) (budget : Budget A) (queue : alloc.vec.Vec stream.CodeBatch)
    (compiled : CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop
      ops before batch 0#usize (.Ok ()) = .ok (submitPack middle worker (.Ok ())))
    (pushed : Budget.push ops middle.budget middle.completed worker = .ok (.Ok (), budget, queue)) :
    CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops before batch =
      .ok (.Ok (), {middle with budget, completed := queue}) := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
  rw [compiled]
  simp only [submitPack, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
    pushed, runtime.compiler.visitor_result.eq]


end Itasca.Runtime.Compiler
