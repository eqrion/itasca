import Exec.Code.Local.Source.TypedStepsWasm1
import Exec.Code.Local.Source.TypedStepsWasm2
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

/-- Fold the compiler invariant through actual successful Wasm 1.0 steps,
retaining the final typed validator state for function completion. -/
theorem TypedRunWasm1.fold {V : Type} {visitor : code.OpVisitor V}
    {data env ctx bt st before after}
    (run : TypedRunWasm1 visitor data env ctx bt st before after)
    (invariant : code.OpIterState → V → Prop) (initial : invariant st before)
    (preserved : ∀ st before next out middle,
      Wasm1.State data env ctx bt st → invariant st before →
      ∀ pending : Wasm1.Pending data env ctx bt {st with pos := next},
      pending.start = st.pos → next.val = st.pos.val + 1 →
      code.step visitor {st with pos := next} data env ctx
        (data.val[pending.start.val]'pending.inbounds) before = .ok (.Ok (), out, middle) →
      Wasm1.State data env ctx bt out → invariant out middle) :
    ∃ finalState, invariant finalState after ∧ Wasm1.State data env ctx bt finalState ∧
      finalState.ctrls.val = [] ∧ finalState.pos = Slice.len data := by
  induction run with
  | done typed closed finished => exact ⟨_, initial, typed, closed, finished⟩
  | step typed pending start advance called rest ih =>
    apply ih
    apply preserved _ _ _ _ _ typed initial pending start advance called
    cases rest <;> assumption

/-- Wasm 2.0 folds the same invariant over the actual indexed-signature steps. -/
theorem TypedRunWasm2.fold {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after}
    (run : TypedRunWasm2 visitor data env ctx index st before after)
    (invariant : code.BodyState → V → Prop) (initial : invariant st before)
    (preserved : ∀ st before next out middle,
      Wasm2.State data env ctx.locals index st → invariant st before →
      ∀ pending : Wasm2.Pending data env ctx.locals index {core := {st.core with pos := next}},
      pending.start = st.core.pos → next.val = st.core.pos.val + 1 →
      code.step_profile visitor {core := {st.core with pos := next}} data env ctx index .Wasm2
        (data.val[pending.start.val]'pending.inbounds) before = .ok (.Ok (), out, middle) →
      Wasm2.State data env ctx.locals index out → invariant out middle) :
    ∃ finalState, invariant finalState after ∧ Wasm2.State data env ctx.locals index finalState ∧
      finalState.blocks.val = [] ∧ finalState.core.pos = Slice.len data := by
  induction run with
  | done typed closed finished => exact ⟨_, initial, typed, closed, finished⟩
  | step typed pending start advance called rest ih =>
    apply ih
    apply preserved _ _ _ _ _ typed initial pending start advance called
    cases rest <;> assumption

/-- Profile-selected typed instruction run from actual initialization. -/
def ProfileTypedBody {V : Type} (visitor : code.OpVisitor V) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (before after : V) : Prop :=
  match profile with
  | .Wasm1 => TypedRunWasm1 visitor data env ctx (Wasm1.Loop.initialBlockType ctx.results.val)
      (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)) before after
  | .Wasm2 => TypedRunWasm2 visitor data env ctx index (Wasm2.initial index) before after

theorem witness_typed_steps {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile) :
    ProfileTypedBody visitor profile w.body env w.ctx w.typeIdx w.startedState after := by
  cases profile with
  | Wasm1 => exact typed_body_wasm1 visitor w.body env w.ctx w.startedState after w.body_accepted
  | Wasm2 => exact typed_body_wasm2 visitor w.body env w.ctx w.typeIdx w.startedState after w.body_accepted

/-- Successful real entry validation exposes both the exact start callback and
the typed instruction steps used to preserve the compiler's source relation. -/
theorem entry_typed_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (start : Usize) (env : module.Env) (index finish : Usize)
    (before after : V) (bounds : CodeEntry.Bounds env) (profile : ValidationProfile)
    (accepted : module.validate_code_entry_with visitor data start env index profile before = .ok (.Ok finish, after)) :
    ∃ w : CodeEntry.Witness visitor data env index start finish before after profile,
      ProfileTypedBody visitor profile w.body env w.ctx w.typeIdx w.startedState after := by
  obtain ⟨w⟩ := module.validate_code_entry_with.witness_profile visitor data start env index finish before after bounds profile accepted
  exact ⟨w, witness_typed_steps w⟩

/-- The same typed run is obtained from the issued batch's actual successful
validation, with its checked function index and original framing witness. -/
theorem batch_typed_steps {V : Type} (visitor : code.OpVisitor V)
    (batch afterBatch : stream.CodeBatch) (index : Usize) (before after : V)
    (bounds : CodeEntry.Bounds batch.env)
    (accepted : stream.CodeBatch.validate_func visitor batch index before = .ok (.Ok (), afterBatch, after)) :
    ∃ finish, index.val = batch.first_func.val + batch.num_validated.val ∧
      ∃ w : CodeEntry.Witness visitor batch.code batch.env index batch.validated_end finish before after batch.profile,
        ProfileTypedBody visitor batch.profile w.body batch.env w.ctx w.typeIdx w.startedState after := by
  have cases := stream.CodeBatch.validate_func.cases visitor batch afterBatch index before after (.Ok ()) accepted
  rcases cases with ⟨error, _, impossible, _⟩ | ⟨_, error, _, impossible, _⟩ | ⟨_, finish, count, next, _, _, _⟩
  · cases impossible
  · cases impossible
  · obtain ⟨_, position, entry⟩ := stream.CodeBatch.validate_next.accepted visitor batch index finish before after next
    exact ⟨finish, position, entry_typed_steps visitor batch.code batch.validated_end batch.env index finish
      before after bounds batch.profile entry⟩
end Exec.Code
