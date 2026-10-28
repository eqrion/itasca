import Itasca.Runtime.Code.Local.Source.TypedStepsWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca

/-- An accepted body of either profile has the Wasm 2.0 typed instruction run from its actual
initialization, since an accepted Wasm 1.0 body is accepted by the Wasm 2.0 reader with the same
callbacks. -/
theorem witness_typed_steps {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile) :
    TypedRunWasm2 visitor w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) w.startedState after := by
  have accepted := w.body_accepted
  cases profile with
  | Wasm1 =>
    exact typed_body_wasm2 visitor w.body env w.ctx w.typeIdx w.startedState after
      (code.validate_body_with.wasm1_accepted _ _ _ _ _ _ _ accepted)
  | Wasm2 => exact typed_body_wasm2 visitor w.body env w.ctx w.typeIdx w.startedState after accepted

/-- Successful real entry validation exposes both the exact start callback and
the typed instruction steps used to preserve the compiler's source relation. -/
theorem entry_typed_steps {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (start : Usize) (env : module.Env) (index finish : Usize)
    (before after : V) (bounds : CodeEntry.Bounds env) (profile : ValidationProfile)
    (accepted : module.validate_code_entry_with visitor data start env index profile before = .ok (.Ok finish, after)) :
    ∃ w : CodeEntry.Witness visitor data env index start finish before after profile,
      TypedRunWasm2 visitor w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) w.startedState after := by
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
        TypedRunWasm2 visitor w.body batch.env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) w.startedState after := by
  have cases := stream.CodeBatch.validate_func.cases visitor batch afterBatch index before after (.Ok ()) accepted
  rcases cases with ⟨error, _, impossible, _⟩ | ⟨_, error, _, impossible, _⟩ | ⟨_, finish, count, next, _, _, _⟩
  · cases impossible
  · cases impossible
  · obtain ⟨_, position, entry⟩ := stream.CodeBatch.validate_next.accepted visitor batch index finish before after next
    exact ⟨finish, position, entry_typed_steps visitor batch.code batch.validated_end batch.env index finish
      before after bounds batch.profile entry⟩
end Itasca.Runtime.Code
