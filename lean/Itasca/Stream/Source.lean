import Itasca.Support.Result
import Itasca.Profile.BinaryUnique
import Itasca.Module.Code.LocalsComplete
import Itasca.Contracts
import Itasca.Module.Readers.Types

/-!
Sections, each formerly its own module: Batch, BatchTotal, BatchComplete, Source.
-/

/-! ## Batch -/

section

/-!
# Worker batches

Properties of the `stream.CodeBatch` workers that the driver issues. `StreamBatch.Issued`, the
immutable state of an issued batch, and `StreamBatch.Reachable`, the workers obtainable from its
seed through actual batch operations, are defined in `Itasca/Contracts`.
`StreamBatch.Reachable.validation` extracts a `StreamBatch.Prefix` of successful entry
validations from any reachable worker, `StreamBatch.Reachable.finished` shows that a worker
accepted by `stream.CodeBatch.finish` has validated every entry in order and consumed exactly its
bytes, and `stream.CodeBatch.validate_func.cases` gives the complete case split of one validation
call.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamBatch

/-- Successful entry executions in byte and defined-function order. Dispatch
is absent from this relation because a worker can validate before dispatching. -/
inductive Prefix (issued : Issued) : Nat → Usize → Prop where
  | nil : Prefix issued 0 0#usize
  | snoc {V : Type} (visitor : code.OpVisitor V) {v v' count pos index finish} :
      Prefix issued count pos → index.val = issued.first_func.val + count →
      metadata.validate_code_entry_with visitor issued.code pos issued.env index v =
        .ok (.Ok finish, v') →
      Prefix issued (count + 1) finish

/-- The part of a worker record that operations cannot change. -/
def Identity (issued : Issued) (batch : stream.CodeBatch) : Prop :=
  batch.module_id = issued.module_id ∧ batch.batch_id = issued.batch_id ∧
  batch.env = issued.env ∧ batch.code = issued.code ∧
  batch.code_offset = issued.code_offset ∧ batch.first_func = issued.first_func ∧
  batch.num_funcs = issued.num_funcs

end Itasca.StreamBatch

namespace Itasca

/-- `stream.CodeBatch.finish` succeeds exactly when no error is stored, every function was
validated, and validation consumed the whole code view. -/
@[simp] theorem stream.CodeBatch.finish.accepted_iff (batch : stream.CodeBatch) :
    stream.CodeBatch.finish batch = .ok (.Ok ()) ↔
      batch.error = none ∧ batch.num_validated = batch.num_funcs ∧
      batch.validated_end = Slice.len batch.code := by
  simp only [stream.CodeBatch.finish]
  cases he : batch.error <;> simp
  split <;> simp_all
  constructor
  · intro h; apply UScalar.eq_of_val_eq; simpa using h
  · intro h; simpa using congrArg UScalar.val h

/-- A stored error returns verbatim and neither cursor nor visitor changes. -/
theorem stream.CodeBatch.validate_func.sticky {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V) (e : error.Error)
    (h : batch.error = some e) :
    stream.CodeBatch.validate_func visitor batch index v = .ok (.Err e, batch, v) := by
  simp [stream.CodeBatch.validate_func, h, core.option.Option.is_none]
  cases batch
  simp_all

/-- A successful next-function check identifies the actual entry call and
its index, without assumptions about unrelated visitor executions. -/
theorem stream.CodeBatch.validate_next.accepted {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index finish : Usize) (v v' : V)
    (h : stream.CodeBatch.validate_next visitor batch index v = .ok (.Ok finish, v')) :
    batch.num_validated.val < batch.num_funcs.val ∧
    index.val = batch.first_func.val + batch.num_validated.val ∧
    metadata.validate_code_entry_with visitor batch.code batch.validated_end batch.env index v =
      .ok (.Ok finish, v') := by
  unfold stream.CodeBatch.validate_next at h
  split at h
  · simp at h
  · rename_i hcount
    obtain ⟨i, hi, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hadd := UScalar.add_equiv batch.first_func batch.num_validated
    rw [hi] at hadd
    split at h
    · simp at h
    · rename_i hindex
      have heq : index = i := by apply UScalar.eq_of_val_eq; simpa using hindex
      refine ⟨by scalar_tac, ?_, ?_⟩
      · simpa [heq] using hadd.2.1
      · exact h

/-- Complete ordinary-call cases: the first error is stored; only successful
entry validation increments the validation count. -/
theorem stream.CodeBatch.validate_func.cases {V : Type} (visitor : code.OpVisitor V)
    (batch after : stream.CodeBatch) (index : Usize) (v v' : V)
    (r : core.result.Result Unit error.Error)
    (h : stream.CodeBatch.validate_func visitor batch index v = .ok (r, after, v')) :
    (∃ e, batch.error = some e ∧ r = .Err e ∧ after = batch ∧ v' = v) ∨
    (batch.error = none ∧ ∃ e,
      stream.CodeBatch.validate_next visitor batch index v = .ok (.Err e, v') ∧
      r = .Err e ∧ after = { batch with error := some e }) ∨
    (batch.error = none ∧ ∃ finish count,
      stream.CodeBatch.validate_next visitor batch index v = .ok (.Ok finish, v') ∧
      count.val = batch.num_validated.val + 1 ∧ r = .Ok () ∧
      after = { batch with num_validated := count, validated_end := finish }) := by
  cases he : batch.error with
  | some e =>
    rw [stream.CodeBatch.validate_func.sticky visitor batch index v e he] at h
    have hh : r = .Err e ∧ after = batch ∧ v' = v := by simpa [eq_comm] using h
    exact Or.inl ⟨e, rfl, hh⟩
  | none =>
    unfold stream.CodeBatch.validate_func at h
    simp [he, core.option.Option.is_none] at h
    obtain ⟨⟨reply, w⟩, hnext, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases reply with
    | Err e =>
      simp at h
      have hh : r = .Err e ∧ after = { batch with error := some e } ∧ v' = w := by
        simpa [eq_comm] using h
      exact Or.inr (Or.inl ⟨rfl, e, hh.2.2 ▸ hnext, hh.1, hh.2.1⟩)
    | Ok finish =>
      simp at h
      obtain ⟨count, hcount, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hadd := UScalar.add_equiv batch.num_validated 1#usize
      rw [hcount] at hadd
      simp at h
      have hh : r = .Ok () ∧
          after = { batch with num_validated := count, validated_end := finish } ∧ v' = w := by
        simpa [eq_comm, he] using h
      exact Or.inr (Or.inr ⟨rfl, finish, count, hh.2.2 ▸ hnext,
        by simpa using hadd.2.1, hh.1, by simpa [he] using hh.2.1⟩)

/-- Dispatch can change only its own count and byte cursor. -/
theorem stream.CodeBatch.next_entry.cases
    (batch after : stream.CodeBatch) (r : core.result.Result stream.CodeEntry error.Error)
    (h : stream.CodeBatch.next_entry batch = .ok (r, after)) :
    after = batch ∨ ∃ index entry count cursor,
      batch.num_dispatched.val < batch.num_funcs.val ∧
      stream.frame_entry batch.code batch.dispatch_end index batch.code_offset = .ok (.Ok entry) ∧
      count.val = batch.num_dispatched.val + 1 ∧
      cursor.val + batch.code_offset.val = entry.end.val ∧
      after = { batch with num_dispatched := count, dispatch_end := cursor } := by
  unfold stream.CodeBatch.next_entry at h
  split at h
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl h.2.symm
  · rename_i hcount
    obtain ⟨index, _, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨reply, hframe, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases reply with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      exact Or.inl h.2.symm
    | Ok entry =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨cursor, hcursor, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨count, hnext, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hadd := UScalar.add_equiv batch.num_dispatched 1#usize
      rw [hnext] at hadd
      have hsub := UScalar.sub_equiv entry.end batch.code_offset
      rw [hcursor] at hsub
      simp at h
      exact Or.inr ⟨index, entry, count, cursor, by scalar_tac, hframe,
        by simpa using hadd.2.1, by have := hsub.1; have := hsub.2.1; omega, h.2.symm⟩

end Itasca

namespace Itasca.StreamBatch

/-- A reachable worker has the issued identity and its validated bytes form a successful
validation prefix, including after dispatch or a worker error. -/
theorem Reachable.validation {issued : Issued} {batch : stream.CodeBatch}
    (h : Reachable issued batch) :
    Identity issued batch ∧ Prefix issued batch.num_validated.val batch.validated_end ∧
      batch.num_validated.val ≤ issued.num_funcs.val := by
  induction h with
  | seed => exact ⟨by simp [Identity, Issued.seed], .nil, by simp [Issued.seed]⟩
  | @dispatch before after result previous run ih =>
    rcases stream.CodeBatch.next_entry.cases before after result run with rfl | hcase
    · exact ih
    · obtain ⟨_, _, count, cursor, _, _, _, _, rfl⟩ := hcase
      exact ih
  | @validate V visitor before after index v v' result previous run ih =>
    rcases stream.CodeBatch.validate_func.cases visitor before after index v v' result run with
      sticky | failure | success
    · obtain ⟨_, _, _, rfl, _⟩ := sticky
      exact ih
    · obtain ⟨_, _, _, _, rfl⟩ := failure
      exact ih
    · obtain ⟨_, finish, count, hnext, hn, _, rfl⟩ := success
      obtain ⟨hcount, hindex, hentry⟩ :=
        stream.CodeBatch.validate_next.accepted visitor before index finish v v' hnext
      have hid := ih.1
      obtain ⟨_, _, henv, hcode, _, hfirst, hnum⟩ := hid
      refine ⟨ih.1, ?_, ?_⟩
      · change Prefix issued count.val finish
        rw [hn]
        exact ih.2.1.snoc visitor (by simpa [hfirst] using hindex)
          (by simpa [henv, hcode] using hentry)
      · change count.val ≤ issued.num_funcs.val
        rw [hn]
        rw [hnum] at hcount
        omega

/-- The successful prefix yields independent encodings and generated typing
by applying entry soundness to every actual successful validation call. -/
theorem Prefix.typed {issued : Issued} {count : Nat} {finish : Usize}
    (h : Prefix issued count finish) (hbound : CodeEntry.Bounds issued.env) :
    ∃ entries, entries.length = count ∧
      ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding))
        issued.code 0#usize entries finish ∧
      ModuleCode.EntriesTyped issued.env issued.first_func.val entries := by
  induction h with
  | nil => exact ⟨[], rfl, ⟨[], .nil, Wasm1.BytesAt.nil _ _ (by simp)⟩, .nil _⟩
  | @snoc V visitor v v' count pos index finish previous hindex hentry ih =>
    have hs := metadata.validate_code_entry_with.profile_sound visitor issued.code pos
      issued.env index finish v v' hbound hentry
    obtain ⟨entries, hlen, hbytes, htyped⟩ := ih
    obtain ⟨entry, he, hi, ht, hl⟩ := hs
    refine ⟨entries ++ [entry], by simp [hlen], ModuleCode.entries_at_snoc hbytes he,
      htyped.snoc ?_⟩
    have hentryAt : ModuleCode.EntryAt issued.env index.val entry := ⟨hi, ht.core, hl⟩
    simpa [hindex, hlen] using hentryAt

/-- Finishing a reachable batch implies validation of every entry, in order,
and consumption of exactly its issued bytes. No premise prevalidates workers. -/
theorem Reachable.finished {issued : Issued} {batch : stream.CodeBatch}
    (h : Reachable issued batch) (hbound : CodeEntry.Bounds issued.env)

    (hfinish : stream.CodeBatch.finish batch = .ok (.Ok ())) :
    ∃ entries, entries.length = issued.num_funcs.val ∧
      ModuleBinary.Rep (Profile.CodeEncoding) entries issued.code.val ∧
      ModuleCode.EntriesTyped issued.env issued.first_func.val entries := by
  obtain ⟨hid, hp, _⟩ := h.validation
  have hf := (stream.CodeBatch.finish.accepted_iff batch).mp hfinish
  obtain ⟨entries, hn, hbytes, ht⟩ := hp.typed hbound
  obtain ⟨_, _, _, hcode, _, _, hnum⟩ := hid
  have hn' : entries.length = issued.num_funcs.val := by rw [hn, hf.2.1, hnum]
  obtain ⟨bytes, he, hb⟩ := hbytes
  have hlast : batch.validated_end = Slice.len issued.code := by simpa [hcode] using hf.2.2
  have hbytes : issued.code.val = bytes := by simpa [hlast] using hb.suffix
  exact ⟨entries, hn', hbytes ▸ he, ht⟩

end Itasca.StreamBatch

end

/-! ## BatchTotal -/

section

/-!
# Worker termination

Termination of `stream.CodeBatch.validate_next`, `stream.CodeBatch.validate_func` and the
whole-batch loop `stream.CodeBatch.validate_all` on arbitrary bytes, given a total visitor
(`FullVisitor.Total`). `stream.CodeBatch.validate_all.reachable` also shows that the final state is
reachable from the issued seed by actual batch operations.
-/

open Aeneas Aeneas.Std

namespace Itasca
/-- `stream.CodeBatch.validate_next` returns an ordinary result for arbitrary indices and
malformed entry bytes. The declared function interval gives room to compute the expected index. -/
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
    · exact metadata.validate_code_entry_with.profile_total visitor htotal batch.code
        batch.validated_end batch.env index v hbound

/-- `stream.CodeBatch.validate_func` returns an ordinary result, stores worker errors, and cannot
overflow its counter because a successful entry validation occurs only before the batch end. -/
theorem stream.CodeBatch.validate_func.returns {V : Type} (visitor : code.OpVisitor V)
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

/-- Every iteration of the `validate_all` loop calls the extracted `validate_func`, so the state
after each iteration is reachable. The loop terminates because an error clears the running flag
and a successful iteration decreases the number of remaining functions. -/
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
        obtain ⟨⟨reply, after, v⟩, hr⟩ := stream.CodeBatch.validate_func.returns
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

/-- Running `stream.CodeBatch.validate_all` terminates in a reachable state, including on invalid
bytes and stored errors. -/
@[step]
theorem stream.CodeBatch.validate_all.reachable (issued : StreamBatch.Issued)
    (batch : stream.CodeBatch) (hissued : issued.Bounded)
    (hbound : CodeEntry.Bounds issued.env) (hreach : StreamBatch.Reachable issued batch) :
    stream.CodeBatch.validate_all batch ⦃ after => StreamBatch.Reachable issued after ⦄ := by
  obtain ⟨result, hr, after, hafter, rfl⟩ := WP.spec_imp_exists
    (stream.CodeBatch.validate_all_loop.spec issued batch true hissued hbound hreach)
  simpa [stream.CodeBatch.validate_all, hr] using hafter

end Itasca

end

/-! ## BatchComplete -/

section

/-!
# Worker completeness

Completeness of `stream.CodeBatch.validate_func` and `stream.CodeBatch.validate_all`. Independently
encoded and typed entries, together with an accepting visitor (`FullVisitor.Accepts`), make the
actual worker loop succeed. `stream.CodeBatch.validate_all.complete_at_seed` runs an issued batch from
its seed to a reachable state accepted by `stream.CodeBatch.finish`. The premises are about the
module and the visitor, not about a worker that is assumed to succeed.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- An accepting worker validates the independently encoded next entry and
advances exactly one function, without requiring prior dispatch. -/
theorem stream.CodeBatch.validate_func.complete_at {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (batch : stream.CodeBatch) (index : Usize)
    (entry : Code) (finish : Usize) (v : V)
    (herror : batch.error = none) (hcount : batch.num_validated.val < batch.num_funcs.val)
    (hindex : index.val = batch.first_func.val + batch.num_validated.val)
    (hi : index.val < batch.env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed batch.env batch.env.func_type_indices.val[index.val] entry)
    (hlimits : Profile.EnvironmentWithinLimits batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Profile.CodeEncodingWithinLimits) batch.code batch.validated_end entry finish) :
    ∃ count v', count.val = batch.num_validated.val + 1 ∧
      stream.CodeBatch.validate_func visitor batch index v = .ok (.Ok (),
        { batch with num_validated := count, validated_end := finish }, v') := by
  obtain ⟨v', hentry⟩ := metadata.validate_code_entry_with.profile_complete visitor haccept
    batch.code batch.validated_end batch.env index entry finish v hi htyped hlimits hbound hbytes
  obtain ⟨expected, hadd, hexpected⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
  have heq : expected = index := by apply UScalar.eq_of_val_eq; omega
  subst expected
  have hn : ¬ batch.num_validated ≥ batch.num_funcs := by scalar_tac
  have hnext : stream.CodeBatch.validate_next visitor batch index v = .ok (.Ok finish, v') := by
    simp [stream.CodeBatch.validate_next, hn, hadd, hentry]
  obtain ⟨count, hinc, hcountval⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
  refine ⟨count, v', by simpa using hcountval, ?_⟩
  simp [stream.CodeBatch.validate_func, herror, core.option.Option.is_none, hnext, hinc]

/-- Repeated actual validation consumes the independently encoded remaining
entries, in order, and reaches the exact declared function and byte boundary. -/
theorem stream.CodeBatch.validate_all_loop.complete (batch : stream.CodeBatch)
    (entries : List Code) (finish : Usize)
    (herror : batch.error = none)
    (hcount : batch.num_validated.val + entries.length = batch.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped batch.env
      (batch.first_func.val + batch.num_validated.val) entries)
    (hlimits : Profile.EnvironmentWithinLimits batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits)) batch.code batch.validated_end entries finish) :
    stream.CodeBatch.validate_all_loop batch true = .ok
      (batch.module_id, batch.batch_id, batch.env, batch.code, batch.code_offset,
        batch.first_func, batch.num_funcs, batch.num_dispatched, batch.dispatch_end,
        batch.num_funcs, finish, none) := by
  induction entries generalizing batch with
  | nil =>
    have hc : batch.num_validated = batch.num_funcs := by
      apply UScalar.eq_of_val_eq
      simpa using hcount
    have hp := hbytes.rep_nil
    rw [stream.CodeBatch.validate_all_loop, loop]
    simp [stream.CodeBatch.validate_all_loop.body, hc, hp, herror]
  | cons entry entries ih =>
    have hc : batch.num_validated.val < batch.num_funcs.val := by
      simp only [List.length_cons] at hcount
      omega
    cases htyped with
    | cons ht hrest =>
      obtain ⟨hi, ht, _⟩ := ht
      obtain ⟨index, hadd, hindex⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
      obtain ⟨next, hentry, hremaining⟩ := hbytes.rep_cons
      obtain ⟨count, v', hcountval, hstep⟩ := stream.CodeBatch.validate_func.complete_at
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
        batch index entry next () herror hc hindex (by simpa [hindex] using hi)
        (by simpa [hindex] using ht) hlimits hbound hentry
      cases v'
      have hrest' : ModuleCode.EntriesTyped batch.env
          (batch.first_func.val + count.val) entries := by
        convert hrest using 1
        omega
      have hrec := ih { batch with num_validated := count, validated_end := next }
        herror (by simp only [List.length_cons] at hcount; dsimp only; omega)
        hrest' hlimits hbound hremaining
      have hlt : batch.num_validated < batch.num_funcs := by scalar_tac
      rw [stream.CodeBatch.validate_all_loop, loop]
      simpa [stream.CodeBatch.validate_all_loop.body, hlt, hadd, hstep,
        core.result.Result.is_ok, stream.CodeBatch.validate_all_loop] using hrec

/-- Independently encoded and typed batch contents are accepted by running the extracted worker
loop, which ends with every function validated and `error = none`. -/
theorem stream.CodeBatch.validate_all.complete_at (batch : stream.CodeBatch)
    (entries : List Code) (finish : Usize)
    (herror : batch.error = none)
    (hcount : batch.num_validated.val + entries.length = batch.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped batch.env
      (batch.first_func.val + batch.num_validated.val) entries)
    (hlimits : Profile.EnvironmentWithinLimits batch.env) (hbound : CodeEntry.Bounds batch.env)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits)) batch.code batch.validated_end entries finish) :
    stream.CodeBatch.validate_all batch = .ok
      { batch with num_validated := batch.num_funcs, validated_end := finish, error := none } := by
  simp [stream.CodeBatch.validate_all,
    stream.CodeBatch.validate_all_loop.complete batch entries finish herror hcount htyped hlimits hbound hbytes ]

/-- A bounded issued batch whose contents are independently valid runs from its seed to a
reachable state that `stream.CodeBatch.finish` accepts. -/
theorem stream.CodeBatch.validate_all.complete_at_seed (issued : StreamBatch.Issued)
    (entries : List Code) (hissued : issued.Bounded)
    (hcount : entries.length = issued.num_funcs.val)
    (htyped : ModuleCode.EntriesTyped issued.env issued.first_func.val entries)
    (hlimits : Profile.EnvironmentWithinLimits issued.env) (hbound : CodeEntry.Bounds issued.env)
    (hbytes : Rep (Profile.CodeEncodingWithinLimits) entries issued.code.val) :
    ∃ after, stream.CodeBatch.validate_all issued.seed = .ok after ∧
      StreamBatch.Reachable issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) := by
  have hb : At (Rep (Profile.CodeEncodingWithinLimits)) issued.code 0#usize entries
      (Slice.len issued.code) := ⟨issued.code.val, hbytes, by constructor <;> simp⟩
  have hr := stream.CodeBatch.validate_all.complete_at issued.seed entries (Slice.len issued.code)
    rfl (by simpa [StreamBatch.Issued.seed] using hcount)
    (by simpa [StreamBatch.Issued.seed] using htyped) hlimits hbound hb
  have hs := stream.CodeBatch.validate_all.reachable issued issued.seed hissued hbound .seed
  rw [hr] at hs
  simp only [WP.spec_ok] at hs
  refine ⟨_, hr, hs, ?_⟩
  apply (stream.CodeBatch.finish.accepted_iff _).mpr
  simp [StreamBatch.Issued.seed]

end Itasca

end

/-! ## Source -/

section

/-!
# Streaming sources

Lemmas for the helpers that read from a `stream.Source`. The source premises
`StreamSource.Coherent`, `StreamSource.Available` and `StreamSource.CallbacksTotal` are defined in
`Itasca/Contracts`, and `stream.SliceSource` satisfies all three. The file also covers `limits.add_offset`, `stream.read_len` and `stream.read_exact`, and
the transport of encoded intervals between a bounded view and its parent region.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSource

/-- Postcondition of `stream.read_len`: a returned length is a `U32` LEB128 value decoded from
`data` at `start`, converted to `Usize`. Errors are unconstrained. -/
def LenPost (data : Slice U8) (start : Usize) :
    core.result.Result (Usize × Usize) error.Error → Prop
  | .Ok (len, next) => ∃ value : U32, len.val = value.val ∧
      Leb128.Decoded data start value next
  | .Err _ => True

end Itasca.StreamSource

namespace Itasca

/-- Offset arithmetic is total on arbitrary operands and checks the module cap
before addition, so no machine overflow is possible. -/
@[step]
theorem limits.add_offset.spec (a b : Usize) :
    limits.add_offset a b ⦃ r => match r with
      | .Ok total => total.val = a.val + b.val ∧ total.val ≤ limits.MAX_MODULE_BYTES.val
      | .Err e => e = .ModuleTooLarge ∧ limits.MAX_MODULE_BYTES.val < a.val + b.val ⦄ := by
  unfold limits.add_offset
  step*

theorem limits.add_offset.total (a b : Usize) :
    ∃ r, limits.add_offset a b = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (limits.add_offset.spec a b)
  exact ⟨r, hr⟩

theorem limits.add_offset.complete (a b : Usize)
    (hbound : a.val + b.val ≤ limits.MAX_MODULE_BYTES.val) :
    ∃ total, limits.add_offset a b = .ok (.Ok total) ∧ total.val = a.val + b.val := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (limits.add_offset.spec a b)
  cases r with
  | Ok total => exact ⟨total, hr, hp.1⟩
  | Err e => omega

@[step]
theorem stream.read_len.spec (data : Slice U8) (start : Usize) :
    stream.read_len data start ⦃ StreamSource.LenPost data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => cases e <;> simp [stream.read_len, hr, StreamSource.LenPost]
  | Ok pair =>
    obtain ⟨value, next⟩ := pair
    simp only [stream.read_len, hr, bind_ok]
    step
    exact ⟨value, by scalar_tac, hp⟩

/-- Any LEB128 decoding of a `U32` at `start` is returned by `stream.read_len`. -/
theorem stream.read_len.complete (data : Slice U8) (start next : Usize)
    (value : U32) (h : Leb128.Decoded data start value next) :
    ∃ len, stream.read_len data start = .ok (.Ok (len, next)) ∧ len.val = value.val := by
  have hr := reader.read_u32_leb.complete data start value next h
  have hs : stream.read_len data start ⦃ r =>
      ∃ len, r = .Ok (len, next) ∧ len.val = value.val ⦄ := by
    simp only [stream.read_len, hr, bind_ok]
    step
    exact ⟨_, rfl, by scalar_tac⟩
  obtain ⟨_, hr, len, rfl, hv⟩ := WP.spec_imp_exists hs
  exact ⟨len, hr, hv⟩

/-- Exact reads need only the reached code callback to return, and permit its
ordinary error result. The ordering premise prevents subtraction underflow. -/
@[step]
theorem stream.read_exact.spec {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (horder : first.val ≤ last.val)
    (hreturn : ∃ r, source.code state first last = .ok r) :
    stream.read_exact source state first last ⦃ r => match r with
      | .Ok bytes => source.code state first last = .ok (.Ok bytes) ∧
          bytes.length = last.val - first.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hreturn
  cases r with
  | Err e => simp [stream.read_exact, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok bytes =>
    simp only [stream.read_exact, hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step
    split
    · simp
    · simp only [WP.spec_ok]
      exact ⟨trivial, by scalar_tac⟩

/-- Acceptance reveals the actual successful source call, without a callback
termination premise for this or any other read. -/
theorem stream.read_exact.accepted {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (h : stream.read_exact source state first last = .ok (.Ok bytes)) :
    source.code state first last = .ok (.Ok bytes) ∧ bytes.length = last.val - first.val := by
  have hex : ∃ r, source.code state first last = .ok r := by
    unfold stream.read_exact at h
    obtain ⟨r, hr, _⟩ := ResultFacts.bind_ok_inv _ _ _ h
    exact ⟨r, hr⟩
  have hs := stream.read_exact.spec source state first last horder hex
  simpa [h] using hs

/-- Over a coherent source, a successful exact read returns the requested slice of the code
region. -/
theorem stream.read_exact.sound {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) (hc : StreamSource.Coherent source state environment code tail)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (hbound : last.val ≤ code.length)
    (h : stream.read_exact source state first last = .ok (.Ok bytes)) :
    bytes.val = code.slice first.val last.val ∧ bytes.length = last.val - first.val := by
  obtain ⟨hr, hn⟩ := stream.read_exact.accepted source state first last bytes horder h
  exact ⟨hc.code_eq first last bytes horder hbound hr, hn⟩

/-- A successful code read of the right length is returned by `stream.read_exact`. -/
theorem stream.read_exact.complete {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (hread : source.code state first last = .ok (.Ok bytes))
    (hlen : bytes.length = last.val - first.val) :
    stream.read_exact source state first last = .ok (.Ok bytes) := by
  have hs : stream.read_exact source state first last ⦃ r => r = .Ok bytes ⦄ := by
    simp only [stream.read_exact, hread, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- The concrete slice source returns exact bounded views and rejects other
ranges with an ordinary host error. -/
@[step]
theorem stream.SliceSource.code_spec (state : stream.SliceSource) (first last : Usize) :
    stream.SliceSource.Insts.ItascaStreamSource.code state first last ⦃ r => match r with
      | .Ok bytes => first.val ≤ last.val ∧ last.val ≤ state.code.length ∧
          bytes.val = state.code.val.slice first.val last.val
      | .Err e => e = .Host ∧ (last.val < first.val ∨ state.code.length < last.val) ⦄ := by
  unfold stream.SliceSource.Insts.ItascaStreamSource.code
  step*

/-- `stream.SliceSource` is coherent with its own environment, code and tail slices. -/
theorem stream.SliceSource.coherent (state : stream.SliceSource) :
    StreamSource.Coherent stream.SliceSource.Insts.ItascaStreamSource state
      state.env.val state.code.val state.tail.val := by
  constructor
  · intro bytes h
    have he : state.env = bytes := by
      simpa [stream.SliceSource.Insts.ItascaStreamSource,
        stream.SliceSource.Insts.ItascaStreamSource.environment] using h
    exact congrArg Slice.val he.symm
  · intro len h
    have he : Slice.len state.code = len := by
      simpa [stream.SliceSource.Insts.ItascaStreamSource,
        stream.SliceSource.Insts.ItascaStreamSource.code_len] using h
    simp [← he]
  · intro first last bytes _ _ h
    have hs := stream.SliceSource.code_spec state first last
    change stream.SliceSource.Insts.ItascaStreamSource.code state first last = _ at h
    simp only [h, WP.spec_ok] at hs
    exact hs.2.2
  · intro bytes h
    have he : state.tail = bytes := by
      simpa [stream.SliceSource.Insts.ItascaStreamSource,
        stream.SliceSource.Insts.ItascaStreamSource.tail] using h
    exact congrArg Slice.val he.symm

/-- `stream.SliceSource` makes every in-range read available. -/
theorem stream.SliceSource.available (state : stream.SliceSource) :
    StreamSource.Available stream.SliceSource.Insts.ItascaStreamSource state
      state.env.val state.code.val state.tail.val := by
  constructor
  · exact ⟨state.env, rfl, rfl⟩
  · exact ⟨Slice.len state.code, rfl, rfl⟩
  · intro first last horder hbound
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.SliceSource.code_spec state first last)
    cases r with
    | Ok bytes => exact ⟨bytes, hr, hp.2.2⟩
    | Err e => simp only [Slice.length] at hp; omega
  · exact ⟨state.tail, rfl, rfl⟩

/-- Every `stream.SliceSource` callback returns. -/
theorem stream.SliceSource.callbacks_total (state : stream.SliceSource) :
    StreamSource.CallbacksTotal stream.SliceSource.Insts.ItascaStreamSource state := by
  constructor
  · exact ⟨.Ok state.env, rfl⟩
  · exact ⟨Slice.len state.code, rfl⟩
  · intro first last
    obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (stream.SliceSource.code_spec state first last)
    exact ⟨r, hr⟩
  · exact ⟨.Ok state.tail, rfl⟩

end Itasca

namespace Itasca.Wasm1

/-- A coherent bounded view is an exact interval in its parent region. -/
theorem BytesAt.of_slice_view {data view : Slice U8} {first last : Usize}
    (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val) :
    BytesAt data first view.val last := by
  refine ⟨?_, ?_, hbound⟩
  · rw [hview, List.slice]
    have he : first.val + (last.val - first.val) = last.val := by omega
    simpa only [List.drop_drop, he] using
      (List.take_append_drop (last.val - first.val) (data.val.drop first.val)).symm
  · rw [hview, List.slice_length]
    simp only [Slice.length] at hbound
    omega

/-- An encoded interval in a view is an encoded interval in the parent region at offsets shifted
by the view start. The offsets are given as equalities rather than executable additions. -/
theorem BytesAt.transport {data view : Slice U8} {first last pos next pos' next' : Usize}
    {bytes : List U8} (hview : BytesAt data first view.val last)
    (hbytes : BytesAt view pos bytes next)
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val) :
    BytesAt data pos' bytes next' := by
  have hn : next.val ≤ view.val.length := hbytes.bound
  have hp : pos.val ≤ view.val.length := by have := hbytes.length; omega
  have shift (i : Nat) (hi : i ≤ view.val.length) :
      data.val.drop (first.val + i) = view.val.drop i ++ data.val.drop last.val := by
    rw [← List.drop_drop, hview.suffix, List.drop_append_of_le_length hi]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpos, hnext, shift pos.val hp, shift next.val hn, hbytes.suffix, List.append_assoc]
  · have := hbytes.length
    omega
  · have := hview.length
    have := hview.bound
    omega

end Itasca.Wasm1

namespace Itasca.Leb128

/-- A LEB128 decoding inside a bounded view is a decoding of the parent region at shifted
offsets. Nonminimal encodings and the consumed bytes are preserved. -/
theorem Decoded.of_slice_view {data view : Slice U8} {first last pos next pos' next' : Usize}
    {value : U32} (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val)
    (hd : Decoded view pos value next)
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val) :
    Decoded data pos' value next' := by
  obtain ⟨bytes, hs, hn, hb, he⟩ := hd
  have hspan := (Wasm1.BytesAt.of_slice_view horder hbound hview).transport
    (⟨hs, hn, hb⟩ : Wasm1.BytesAt view pos bytes next) hpos hnext
  exact ⟨bytes, hspan.suffix, hspan.length, hspan.bound, he⟩

end Itasca.Leb128

namespace Itasca.Wasm1

/-- An encoded interval of the parent region that ends inside a view is an encoded interval of
that view at offsets shifted by the view start. -/
theorem BytesAt.restrict {data view : Slice U8} {first last pos next pos' next' : Usize}
    {bytes : List U8} (hview : BytesAt data first view.val last)
    (hbytes : BytesAt data pos' bytes next')
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val)
    (hwithin : next'.val ≤ last.val) :
    BytesAt view pos bytes next := by
  have hn : next.val ≤ view.val.length := by have := hview.length; omega
  have hp : pos.val ≤ view.val.length := by have := hbytes.length; omega
  have shift (i : Nat) (hi : i ≤ view.val.length) :
      data.val.drop (first.val + i) = view.val.drop i ++ data.val.drop last.val := by
    rw [← List.drop_drop, hview.suffix, List.drop_append_of_le_length hi]
  refine ⟨?_, ?_, hn⟩
  · have he := hbytes.suffix
    rw [hpos, hnext, shift pos.val hp, shift next.val hn, ← List.append_assoc] at he
    exact List.append_cancel_right he
  · have := hbytes.length
    omega

end Itasca.Wasm1

namespace Itasca.Leb128

/-- A LEB128 decoding of the parent region that ends inside a bounded view is a decoding of that
view alone. Completeness uses this direction. -/
theorem Decoded.to_slice_view {data view : Slice U8} {first last pos next pos' next' : Usize}
    {value : U32} (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val)
    (hd : Decoded data pos' value next')
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val)
    (hwithin : next'.val ≤ last.val) :
    Decoded view pos value next := by
  obtain ⟨bytes, hs, hn, hb, he⟩ := hd
  have hspan := (Wasm1.BytesAt.of_slice_view horder hbound hview).restrict
    (⟨hs, hn, hb⟩ : Wasm1.BytesAt data pos' bytes next') hpos hnext hwithin
  exact ⟨bytes, hspan.suffix, hspan.length, hspan.bound, he⟩

end Itasca.Leb128

end
