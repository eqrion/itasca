import Itasca.Stream.Batch
import Itasca.Stream.EntryFrame

/-!
# Worker cursor bounds

Bounds on the dispatch and validation cursors of reachable workers, and the totality of the
read-only `stream.CodeBatch` accessors and `stream.CodeBatch.next_entry`.
`StreamBatch.Reachable.dispatched` bounds the dispatch cursor by framing, and
`StreamBatch.Reachable.cursor_bounds` bounds both cursors independently of each other.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamBatch

/-- Framing advances only the dispatch cursor, always inside the issued bytes. -/
theorem Reachable.dispatched {issued : Issued} {batch : stream.CodeBatch}
    (h : Reachable issued batch) :
    batch.num_dispatched.val ≤ issued.num_funcs.val ∧
      batch.dispatch_end.val ≤ issued.code.length := by
  induction h with
  | seed => simp [Issued.seed]
  | @dispatch before after result previous run ih =>
    rcases stream.CodeBatch.next_entry.cases before after result run with rfl | hcase
    · exact ih
    · obtain ⟨index, entry, count, cursor, hc, hf, hn, hp, rfl⟩ := hcase
      have hframe := stream.frame_entry.sound before.code before.dispatch_end index before.code_offset entry hf
      obtain ⟨content, finish, hext, _, _, _, hend, _⟩ := hframe
      have hspan := hext.span
      obtain ⟨_, _, _, hcode, _, _, hnum, _⟩ := previous.validation.1
      dsimp only
      rw [hnum] at hc
      rw [hcode] at hspan
      constructor <;> omega
  | @validate V visitor before after index v v' result previous run ih =>
    rcases stream.CodeBatch.validate_func.cases visitor before after index v v' result run with
      sticky | failure | success
    · obtain ⟨_, _, _, rfl, _⟩ := sticky
      exact ih
    · obtain ⟨_, _, _, _, rfl⟩ := failure
      exact ih
    · obtain ⟨_, _, _, _, _, _, rfl⟩ := success
      exact ih

/-- Both cursors are bounded independently. Validation bytes are bounded by
actual entry soundness; dispatch contributes no validation evidence. -/
theorem Reachable.cursor_bounds {profile : ValidationProfile} {issued : Issued} {batch : stream.CodeBatch}
    (h : Reachable issued batch) (hbound : CodeEntry.Bounds issued.env)
    (hresults : ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft)
    (hprofile : issued.profile = profile) :
    batch.num_dispatched.val ≤ issued.num_funcs.val ∧
    batch.dispatch_end.val ≤ issued.code.length ∧
    batch.num_validated.val ≤ issued.num_funcs.val ∧
    batch.validated_end.val ≤ issued.code.length := by
  obtain ⟨_, hp, hn⟩ := h.validation
  obtain ⟨_, _, he, _⟩ := hp.typed hbound hresults hprofile
  exact ⟨h.dispatched.1, h.dispatched.2, hn, he.span.2⟩

end Itasca.StreamBatch

namespace Itasca

/-- Dispatch returns an ordinary result when function indices fit in `Usize`, including on
malformed bytes and when the dispatch cursor is already exhausted. -/
theorem stream.CodeBatch.next_entry.total (batch : stream.CodeBatch)
    (hindex : batch.first_func.val + batch.num_funcs.val ≤ Usize.max) :
    ∃ r, stream.CodeBatch.next_entry batch = .ok r := by
  have ht : stream.CodeBatch.next_entry batch ⦃ _ => True ⦄ := by
    unfold stream.CodeBatch.next_entry
    split
    · simp
    · rename_i hcount
      step
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
        (stream.frame_entry.spec batch.code batch.dispatch_end index batch.code_offset)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok entry =>
        obtain ⟨content, finish, _, _, _, _, hend, _⟩ := hp
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step*
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists ht
  exact ⟨r, hr⟩

/-- Read-only accessors expose the immutable issued fields. -/
theorem stream.CodeBatch.accessors {issued : StreamBatch.Issued} {batch : stream.CodeBatch}
    (h : StreamBatch.Reachable issued batch) :
    stream.CodeBatch.len batch = .ok issued.num_funcs ∧
    stream.CodeBatch.impl.code batch = .ok issued.code ∧
    stream.CodeBatch.impl.code_offset batch = .ok issued.code_offset ∧
    stream.CodeBatch.is_empty batch = .ok (decide (issued.num_funcs = 0#usize)) := by
  obtain ⟨_, _, _, hcode, hoffset, _, hnum, _⟩ := h.validation.1
  simp [stream.CodeBatch.len, stream.CodeBatch.impl.code, stream.CodeBatch.impl.code_offset,
    stream.CodeBatch.is_empty, hcode, hoffset, hnum]

/-- A worker observes the same policy selected when its batch was issued. -/
theorem stream.CodeBatch.profile_preserved {issued : StreamBatch.Issued} {batch : stream.CodeBatch}
    (h : StreamBatch.Reachable issued batch) :
    stream.CodeBatch.impl.profile batch = .ok issued.profile := by
  obtain ⟨_, _, _, _, _, _, _, hp⟩ := h.validation.1
  simp [stream.CodeBatch.impl.profile, hp]

/-- `stream.CodeBatch.is_last` returns an ordinary result on a reachable worker of a bounded
issued batch. -/
theorem stream.CodeBatch.is_last.total {issued : StreamBatch.Issued} {batch : stream.CodeBatch}
    (hb : issued.Bounded) (h : StreamBatch.Reachable issued batch) :
    ∃ r, stream.CodeBatch.is_last batch = .ok r := by
  obtain ⟨_, _, henv, _, _, hfirst, hnum, _⟩ := h.validation.1
  have ht : stream.CodeBatch.is_last batch ⦃ _ => True ⦄ := by
    unfold stream.CodeBatch.is_last
    rw [hfirst, hnum]
    have hb' := hb.2.1
    step*
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists ht
  exact ⟨r, hr⟩

end Itasca
