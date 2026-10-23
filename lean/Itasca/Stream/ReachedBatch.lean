import Itasca.Module.Code.ReachedEntry
import Itasca.Stream.BatchTotal

namespace Itasca
open Aeneas Aeneas.Std

/-- Batch index checks return before entry callbacks on an invalid index. -/
theorem stream.CodeBatch.validate_next.total_on {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V)
    (range : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (entry : module.validate_code_entry_with visitor batch.code batch.validated_end
      batch.env index batch.profile v ⦃ _ => True ⦄) :
    stream.CodeBatch.validate_next visitor batch index v ⦃ _ => True ⦄ := by
  unfold stream.CodeBatch.validate_next
  split
  · simp
  · obtain ⟨expected,added,_⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
    rw [added]
    simp only [bind_ok]
    split
    · simp
    · exact entry

/-- Worker counter/error bookkeeping needs only the reached entry call to
return; no callbacks on other visitor states are assumed. -/
theorem stream.CodeBatch.validate_func.total_on {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V)
    (range : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (entry : module.validate_code_entry_with visitor batch.code batch.validated_end
      batch.env index batch.profile v ⦃ _ => True ⦄) :
    stream.CodeBatch.validate_func visitor batch index v ⦃ _ => True ⦄ := by
  cases sticky : batch.error with
  | some error => rw [stream.CodeBatch.validate_func.sticky visitor batch index v error sticky]; simp
  | none =>
    obtain ⟨⟨result,after⟩,run,_⟩ := WP.spec_imp_exists
      (stream.CodeBatch.validate_next.total_on visitor batch index v range entry)
    cases result with
    | Err error => simp [stream.CodeBatch.validate_func,sticky,core.option.Option.is_none,run]
    | Ok finish =>
      have remaining := (stream.CodeBatch.validate_next.accepted visitor batch index finish v after run).1
      obtain ⟨count,added,_⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
      simp [stream.CodeBatch.validate_func,sticky,core.option.Option.is_none,run,added]

/-- Complete worker validation reduces to actual decoded entry metadata and
its function-start/body calls, including all malformed-input rejection paths. -/
theorem stream.CodeBatch.validate_func.prepared_total {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V)
    (bounds : CodeEntry.Bounds batch.env)
    (range : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (start : ∀ prepared : CodeEntry.Prepared batch.code batch.env index batch.validated_end batch.profile,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish ⦃ _ => True ⦄)
    (bodyTotal : ∀ (prepared : CodeEntry.Prepared batch.code batch.env index batch.validated_end batch.profile) started,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
      code.validate_body_with visitor prepared.body batch.env prepared.ctx prepared.typeIdx batch.profile started ⦃ _ => True ⦄) :
    stream.CodeBatch.validate_func visitor batch index v ⦃ _ => True ⦄ := by
  exact stream.CodeBatch.validate_func.total_on visitor batch index v range
    (module.validate_code_entry_with.total_on visitor batch.code batch.validated_end batch.env index v
      bounds batch.profile start bodyTotal)
end Itasca
