import Exec.Code.Local.Source.CallbackTrace
import Itasca.Profile.EntrySound
import Itasca.Stream.Batch
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca Itasca.VisitorTrace

theorem CallbackRun.append {V : Type} {visitor : code.OpVisitor V}
    {initial middle final : V} {left right : List (CallbackRecord V)}
    (first : CallbackRun visitor initial left middle)
    (second : CallbackRun visitor middle right final) :
    CallbackRun visitor initial (left ++ right) final := by
  induction second with
  | nil => simpa using first
  | snoc prior called ih => simpa only [List.append_assoc] using CallbackRun.snoc ih called

/-- Fold exact callback equations with an invariant that can retain the whole
processed prefix. No compiler invariant is built into the trace relation. -/
theorem CallbackRun.fold {V : Type} {visitor : code.OpVisitor V}
    {initial final : V} {records : List (CallbackRecord V)}
    (run : CallbackRun visitor initial records final)
    (invariant : List (CallbackRecord V) → V → Prop)
    (start : invariant [] initial)
    (step : ∀ prior before event reply after,
      CallbackRun visitor initial prior before → invariant prior before →
      invoke visitor before event = .ok (reply, after) →
      invariant (prior ++ [⟨before, ⟨event, reply⟩, after⟩]) after) : invariant records final := by
  induction run with
  | nil => exact start
  | snoc prior called ih => exact step _ _ _ _ _ prior ih called

/-- Canonical accepted-body trace, selected by the actual validation profile. -/
def ProfileCallbackBody (profile : ValidationProfile) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (observations : List Observation) : Prop :=
  match profile with
  | .Wasm1 => ∃ bt, ctx.results.val = Control.results bt ∧ VisitorTrace.AcceptedBody data env ctx bt observations
  | .Wasm2 => Wasm2.CallbackTrace.AcceptedBody data env ctx index observations

/-- The actual entry witness retains parser framing and the start callback;
its body receives exact stateful callbacks with independently typed syntax. -/
theorem witness_callbacks {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile)
    (signatures : ∀ ft ∈ env.types.val, Profile.FuncType profile ft) :
    ∃ records, CallbackRun visitor before
      (⟨before, ⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩, w.startedState⟩ :: records) after ∧
      ProfileCallbackBody profile w.body env w.ctx w.typeIdx (records.map CallbackRecord.observation) := by
  have first : CallbackRun visitor before
      [⟨before, ⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩, w.startedState⟩] w.startedState :=
    .snoc (.nil before) w.function_start
  cases profile with
  | Wasm1 =>
    have member : w.ft ∈ env.types.val := by rw [← w.function_type]; exact List.getElem_mem _
    obtain ⟨bt, shape⟩ := CodeEntry.blockType_of_length w.ft.results.val (signatures _ member)
    have results := w.context_results.trans shape
    obtain ⟨records, callbacks, trace⟩ := callback_body_wasm1 visitor w.body env w.ctx bt results
      w.startedState after w.body_accepted
    exact ⟨records, by simpa using first.append callbacks, bt, results, trace⟩
  | Wasm2 =>
    obtain ⟨records, callbacks, trace⟩ := callback_body_wasm2 visitor w.body env w.ctx w.typeIdx
      w.startedState after w.body_accepted
    exact ⟨records, by simpa using first.append callbacks, trace⟩

/-- A successful real entry validation exposes its exact callback-state trace,
including the function-start event and the validator's operand/control states. -/
theorem entry_callbacks {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (start : Usize) (env : module.Env) (index finish : Usize)
    (before after : V) (bounds : CodeEntry.Bounds env) (profile : ValidationProfile)
    (signatures : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (accepted : module.validate_code_entry_with visitor data start env index profile before = .ok (.Ok finish, after)) :
    ∃ w : CodeEntry.Witness visitor data env index start finish before after profile,
      ∃ records, CallbackRun visitor before
        (⟨before, ⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩, w.startedState⟩ :: records) after ∧
        ProfileCallbackBody profile w.body env w.ctx w.typeIdx (records.map CallbackRecord.observation) := by
  obtain ⟨w⟩ := module.validate_code_entry_with.witness_profile visitor data start env index finish before after bounds profile accepted
  exact ⟨w, witness_callbacks w signatures⟩

/-- Successful issued-batch validation exposes the entry parser and the same
stateful callbacks; no visitor totality or compiler correctness is assumed. -/
theorem batch_callbacks {V : Type} (visitor : code.OpVisitor V)
    (batch afterBatch : stream.CodeBatch) (index : Usize) (before after : V)
    (bounds : CodeEntry.Bounds batch.env)
    (signatures : ∀ ft ∈ batch.env.types.val, Profile.FuncType batch.profile ft)
    (accepted : stream.CodeBatch.validate_func visitor batch index before = .ok (.Ok (), afterBatch, after)) :
    ∃ finish, index.val = batch.first_func.val + batch.num_validated.val ∧
      ∃ w : CodeEntry.Witness visitor batch.code batch.env index batch.validated_end finish before after batch.profile,
        ∃ records, CallbackRun visitor before
          (⟨before, ⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩, w.startedState⟩ :: records) after ∧
          ProfileCallbackBody batch.profile w.body batch.env w.ctx w.typeIdx (records.map CallbackRecord.observation) := by
  have cases := stream.CodeBatch.validate_func.cases visitor batch afterBatch index before after (.Ok ()) accepted
  rcases cases with ⟨error, _, impossible, _⟩ | ⟨_, error, _, impossible, _⟩ | ⟨_, finish, count, next, _, _, _⟩
  · cases impossible
  · cases impossible
  · obtain ⟨_, position, entry⟩ := stream.CodeBatch.validate_next.accepted visitor batch index finish before after next
    exact ⟨finish, position, entry_callbacks visitor batch.code batch.validated_end batch.env index finish
      before after bounds batch.profile signatures entry⟩

/-- Specialize the batch bridge to the actual extracted FunctionCompiler
visitor dictionary used by CompileScheduler.compile_entry. -/
theorem function_compiler_callbacks {A : Type} (allocator : runtime.platform.Alloc A)
    (batch afterBatch : stream.CodeBatch) (index : Usize)
    (before after : runtime.compiler.FunctionCompiler A)
    (bounds : CodeEntry.Bounds batch.env)
    (signatures : ∀ ft ∈ batch.env.types.val, Profile.FuncType batch.profile ft)
    (accepted : stream.CodeBatch.validate_func
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator) batch index before = .ok (.Ok (), afterBatch, after)) :
    ∃ finish, index.val = batch.first_func.val + batch.num_validated.val ∧
      ∃ w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator)
          batch.code batch.env index batch.validated_end finish before after batch.profile,
        ∃ records, CallbackRun (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor allocator) before
          (⟨before, ⟨.functionStart w.ctx w.typeIdx w.bodyStart finish, .Ok ()⟩, w.startedState⟩ :: records) after ∧
          ProfileCallbackBody batch.profile w.body batch.env w.ctx w.typeIdx (records.map CallbackRecord.observation) :=
  batch_callbacks _ batch afterBatch index before after bounds signatures accepted
end Exec.Code
