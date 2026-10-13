import Itasca.Support.Result
import Itasca.Profile.EntrySound
import Itasca.Module.Code.EntryVisitor
import Itasca.Module.Code.Section

/-!
# Worker batches

Models the `stream.CodeBatch` workers that the driver issues. `StreamBatch.Issued` is the immutable
state of an issued batch, and `StreamBatch.Reachable` holds for every worker obtainable from its
seed through actual `stream.CodeBatch.next_entry` and `stream.CodeBatch.validate_func` executions.
`StreamBatch.Reachable.validation` extracts a `StreamBatch.Prefix` of successful entry
validations from any reachable worker, `StreamBatch.Reachable.finished` shows that a worker
accepted by `stream.CodeBatch.finish` has validated every entry in order and consumed exactly its
bytes, and `stream.CodeBatch.validate_func.cases` gives the complete case split of one validation
call. Both profiles are covered through the `profile` parameter.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamBatch

/-- Immutable description of the exact state issued by the driver. -/
structure Issued where
  module_id : U64
  batch_id : Usize
  env : module.Env
  code : Slice U8
  code_offset : Usize
  first_func : Usize
  num_funcs : Usize
  profile : ValidationProfile

/-- Workers begin with independent zeroed dispatch and validation cursors. -/
def Issued.seed (issued : Issued) : stream.CodeBatch :=
  { module_id := issued.module_id, batch_id := issued.batch_id,
    profile := issued.profile, env := issued.env, code := issued.code, code_offset := issued.code_offset,
    first_func := issued.first_func, num_funcs := issued.num_funcs,
    num_dispatched := 0#usize, dispatch_end := 0#usize,
    num_validated := 0#usize, validated_end := 0#usize, error := none }

/-- Bounds supplied by framing and the actual environment decode, separately
from the operation history of a worker. -/
def Issued.Bounded (issued : Issued) : Prop :=
  0 < issued.num_funcs.val ∧
  issued.first_func.val + issued.num_funcs.val ≤ issued.env.func_type_indices.val.length ∧
  issued.code_offset.val + issued.code.length ≤ limits.MAX_MODULE_BYTES.val

/-- Every change is an ordinary result of a real extracted batch method.
No constructor can assign a validation cursor or assert successful finishing. -/
inductive Reachable (issued : Issued) : stream.CodeBatch → Prop where
  | seed : Reachable issued issued.seed
  | dispatch {before after result} : Reachable issued before →
      stream.CodeBatch.next_entry before = .ok (result, after) → Reachable issued after
  | validate {V : Type} (visitor : code.OpVisitor V) {before after index v v' result} :
      Reachable issued before →
      stream.CodeBatch.validate_func visitor before index v = .ok (result, after, v') →
      Reachable issued after

/-- Successful entry executions in byte and defined-function order. Dispatch
is absent from this relation because a worker can validate before dispatching. -/
inductive Prefix (issued : Issued) : Nat → Usize → Prop where
  | nil : Prefix issued 0 0#usize
  | snoc {V : Type} (visitor : code.OpVisitor V) {v v' count pos index finish} :
      Prefix issued count pos → index.val = issued.first_func.val + count →
      module.validate_code_entry_with visitor issued.code pos issued.env index issued.profile v =
        .ok (.Ok finish, v') →
      Prefix issued (count + 1) finish

/-- The part of a worker record that operations cannot change. -/
def Identity (issued : Issued) (batch : stream.CodeBatch) : Prop :=
  batch.module_id = issued.module_id ∧ batch.batch_id = issued.batch_id ∧
  batch.env = issued.env ∧ batch.code = issued.code ∧
  batch.code_offset = issued.code_offset ∧ batch.first_func = issued.first_func ∧
  batch.num_funcs = issued.num_funcs ∧ batch.profile = issued.profile

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

/-- `stream.CodeBatch.finish` returns an ordinary result on every batch. -/
theorem stream.CodeBatch.finish.total (batch : stream.CodeBatch) :
    ∃ r, stream.CodeBatch.finish batch = .ok r := by
  unfold stream.CodeBatch.finish
  split
  · split
    · dsimp only
      split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

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
    module.validate_code_entry_with visitor batch.code batch.validated_end batch.env index batch.profile v =
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
      obtain ⟨_, _, henv, hcode, _, hfirst, hnum, hprofile⟩ := hid
      refine ⟨ih.1, ?_, ?_⟩
      · change Prefix issued count.val finish
        rw [hn]
        exact ih.2.1.snoc visitor (by simpa [hfirst] using hindex)
          (by simpa [henv, hcode, hprofile] using hentry)
      · change count.val ≤ issued.num_funcs.val
        rw [hn]
        rw [hnum] at hcount
        omega

/-- The successful prefix yields independent encodings and generated typing
by applying entry soundness to every actual successful validation call. -/
theorem Prefix.typed {profile : ValidationProfile} {issued : Issued} {count : Nat} {finish : Usize}
    (h : Prefix issued count finish) (hbound : CodeEntry.Bounds issued.env)
    (hresults : ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft)
    (hprofile : issued.profile = profile) :
    ∃ entries, entries.length = count ∧
      ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile))
        issued.code 0#usize entries finish ∧
      ModuleCode.EntriesTyped (profile := profile) issued.env issued.first_func.val entries := by
  induction h with
  | nil => exact ⟨[], rfl, ⟨[], .nil, Wasm1.BytesAt.nil _ _ (by simp)⟩, .nil _⟩
  | @snoc V visitor v v' count pos index finish previous hindex hentry ih =>
    have hs := module.validate_code_entry_with.profile_sound visitor issued.code pos
      issued.env index finish v v' hbound profile hresults (by simpa [hprofile] using hentry)
    obtain ⟨entries, hlen, hbytes, htyped⟩ := ih
    obtain ⟨entry, he, hi, ht, hl⟩ := hs
    refine ⟨entries ++ [entry], by simp [hlen], ModuleCode.entries_at_snoc hbytes he,
      htyped.snoc ?_⟩
    have hentryAt : ModuleCode.EntryAt (profile := profile) issued.env index.val entry := ⟨hi, ht.core, hl⟩
    simpa [hindex, hlen] using hentryAt

/-- Finishing a reachable batch implies validation of every entry, in order,
and consumption of exactly its issued bytes. No premise prevalidates workers. -/
theorem Reachable.finished {profile : ValidationProfile} {issued : Issued} {batch : stream.CodeBatch}
    (h : Reachable issued batch) (hbound : CodeEntry.Bounds issued.env)
    (hresults : ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft)
    (hprofile : issued.profile = profile)
    (hfinish : stream.CodeBatch.finish batch = .ok (.Ok ())) :
    ∃ entries, entries.length = issued.num_funcs.val ∧
      ModuleBinary.Rep (Profile.CodeEncoding profile) entries issued.code.val ∧
      ModuleCode.EntriesTyped (profile := profile) issued.env issued.first_func.val entries := by
  obtain ⟨hid, hp, _⟩ := h.validation
  have hf := (stream.CodeBatch.finish.accepted_iff batch).mp hfinish
  obtain ⟨entries, hn, hbytes, ht⟩ := hp.typed hbound hresults hprofile
  obtain ⟨_, _, _, hcode, _, _, hnum, _⟩ := hid
  have hn' : entries.length = issued.num_funcs.val := by rw [hn, hf.2.1, hnum]
  obtain ⟨bytes, he, hb⟩ := hbytes
  have hlast : batch.validated_end = Slice.len issued.code := by simpa [hcode] using hf.2.2
  have hbytes : issued.code.val = bytes := by simpa [hlast] using hb.suffix
  exact ⟨entries, hn', hbytes ▸ he, ht⟩

end Itasca.StreamBatch
