import Itasca.Stream.StreamBatch

open Aeneas Aeneas.Std

namespace Itasca

/-- Arbitrary indices and malformed entry bytes still produce ordinary results;
the declaration interval supplies room for computing the expected index. -/
theorem stream.CodeBatch.validate_next.total {V : Type} (visitor : code.OpVisitor V)
    (htotal : FullVisitor.Total visitor) (batch : stream.CodeBatch) (index : Usize) (v : V)
    (hbound : CodeEntry.Bounds batch.env)
    (hrange : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length) :
    ∃ r, stream.CodeBatch.validate_next visitor batch index v = .ok r := by
  unfold stream.CodeBatch.validate_next
  split
  · exact ⟨_, rfl⟩
  · rename_i hcount
    obtain ⟨expected, hadd, _⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
    rw [hadd]
    simp only [bind_ok]
    split
    · exact ⟨_, rfl⟩
    · exact module.validate_code_entry_with.total visitor htotal batch.code
        batch.validated_end batch.env index v hbound

/-- Validation records ordinary worker errors and cannot overflow its counter:
successful entry validation occurs only strictly before the batch's end. -/
theorem stream.CodeBatch.validate_func.total {V : Type} (visitor : code.OpVisitor V)
    (htotal : FullVisitor.Total visitor) (batch : stream.CodeBatch) (index : Usize) (v : V)
    (hbound : CodeEntry.Bounds batch.env)
    (hrange : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length) :
    ∃ r, stream.CodeBatch.validate_func visitor batch index v = .ok r := by
  cases he : batch.error with
  | some e => exact ⟨_, stream.CodeBatch.validate_func.sticky visitor batch index v e he⟩
  | none =>
    obtain ⟨⟨r, v'⟩, hr⟩ :=
      stream.CodeBatch.validate_next.total visitor htotal batch index v hbound hrange
    cases r with
    | Err e =>
      exact ⟨(.Err e, { batch with error := some e }, v'), by
        simp [stream.CodeBatch.validate_func, he, core.option.Option.is_none, hr]⟩
    | Ok finish =>
      have hc := (stream.CodeBatch.validate_next.accepted visitor batch index finish v v' hr).1
      obtain ⟨count, hadd, _⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
      exact ⟨(.Ok (), { batch with num_validated := count, validated_end := finish, error := none }, v'), by
        simp [stream.CodeBatch.validate_func, he, core.option.Option.is_none, hr, hadd]⟩

private theorem validate_func_count {V : Type} (visitor : code.OpVisitor V)
    (batch after : stream.CodeBatch) (index : Usize) (v v' : V)
    (r : core.result.Result Unit error.Error)
    (h : stream.CodeBatch.validate_func visitor batch index v = .ok (r, after, v')) :
    match r with
      | .Ok () => after.num_validated.val = batch.num_validated.val + 1
      | .Err _ => after.num_validated = batch.num_validated := by
  rcases stream.CodeBatch.validate_func.cases visitor batch after index v v' r h with
    sticky | failure | success
  · obtain ⟨_, _, rfl, rfl, _⟩ := sticky
    rfl
  · obtain ⟨_, _, _, rfl, rfl⟩ := failure
    rfl
  · obtain ⟨_, _, _, _, hc, rfl, rfl⟩ := success
    exact hc

/-- Every iteration uses the extracted validation method. An error decreases
the stopping flag; a successful iteration decreases the remaining count. -/
theorem stream.CodeBatch.validate_all_loop.spec (issued : StreamBatch.Issued)
    (batch : stream.CodeBatch) (running : Bool)
    (hissued : issued.Bounded) (hbound : CodeEntry.Bounds issued.env)
    (hreach : StreamBatch.Reachable issued batch) :
    stream.CodeBatch.validate_all_loop batch running ⦃ result =>
      ∃ after : stream.CodeBatch, StreamBatch.Reachable issued after ∧
        result = (after.module_id, after.batch_id, after.env, after.code,
          after.code_offset, after.first_func, after.num_funcs, after.num_dispatched,
          after.dispatch_end, after.num_validated, after.validated_end, after.error) ⦄ := by
  unfold stream.CodeBatch.validate_all_loop
  apply loop.spec_decr_nat
    (fun s => issued.num_funcs.val - s.1.num_validated.val + if s.2 then 1 else 0)
    (fun s => StreamBatch.Reachable issued s.1)
  · rintro ⟨current, running⟩ hcurrent
    dsimp only
    have hidentity := hcurrent.validation.1
    obtain ⟨_, _, henv, _, _, hfirst, hnum⟩ := hidentity
    dsimp only at henv hfirst hnum
    have hrange : current.first_func.val + current.num_funcs.val ≤
        current.env.func_type_indices.val.length := by
      rw [henv, hfirst, hnum]
      exact hissued.2.1
    unfold stream.CodeBatch.validate_all_loop.body
    split
    · rename_i hcount
      split
      · step
        obtain ⟨⟨reply, after, v⟩, hr⟩ := stream.CodeBatch.validate_func.total
          code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
          current index () (by simpa [henv] using hbound) hrange
        cases v
        have hafter : StreamBatch.Reachable issued after :=
          .validate code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor hcurrent hr
        have hc := validate_func_count code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
          current after index () () reply hr
        rw [hr]
        cases reply with
        | Err e =>
          simp [core.result.Result.is_ok]
          refine ⟨hafter, ?_⟩
          dsimp only at hc
          simp only [hc]
          scalar_tac
        | Ok u =>
          cases u
          simp [core.result.Result.is_ok]
          refine ⟨hafter, ?_⟩
          dsimp only at hc
          scalar_tac
      · exact ⟨current, hcurrent, rfl⟩
    · exact ⟨current, hcurrent, rfl⟩
  · exact hreach

/-- Complete worker execution terminates and remains reachable by actual
batch operations, including on invalid bytes and sticky errors. -/
@[step]
theorem stream.CodeBatch.validate_all.spec (issued : StreamBatch.Issued)
    (batch : stream.CodeBatch) (hissued : issued.Bounded)
    (hbound : CodeEntry.Bounds issued.env) (hreach : StreamBatch.Reachable issued batch) :
    stream.CodeBatch.validate_all batch ⦃ after => StreamBatch.Reachable issued after ⦄ := by
  obtain ⟨result, hr, after, hafter, rfl⟩ := WP.spec_imp_exists
    (stream.CodeBatch.validate_all_loop.spec issued batch true hissued hbound hreach)
  simpa [stream.CodeBatch.validate_all, hr] using hafter

theorem stream.CodeBatch.validate_all.total (issued : StreamBatch.Issued)
    (batch : stream.CodeBatch) (hissued : issued.Bounded)
    (hbound : CodeEntry.Bounds issued.env) (hreach : StreamBatch.Reachable issued batch) :
    ∃ after, stream.CodeBatch.validate_all batch = .ok after ∧
      StreamBatch.Reachable issued after :=
  WP.spec_imp_exists (stream.CodeBatch.validate_all.spec issued batch hissued hbound hreach)

end Itasca
