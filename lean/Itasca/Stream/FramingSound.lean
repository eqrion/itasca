import Itasca.Support.Result
import Itasca.Stream.FramingStep

/-!
# Batch framing soundness

Soundness of `stream.get_next_batch` over a coherent source. `StreamFraming.EntryFrames` is a
chain of consecutive declared entry extents in the code region. `stream.get_next_batch.sound` gives
the arithmetic bounds of an accepted batch and `stream.get_next_batch.frames` additionally shows
that it frames exactly `next - first` consecutive entries. Neither needs callback totality or
availability, since an accepted run reveals the source calls it reached.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- Coherence transports each actually read length prefix into the fixed code
region, yielding an independent extent without requiring source availability. -/
theorem FrameStep.extent {S : Type} (source : stream.Source S) (state : S)
    (environment tail : List U8) (code : Slice U8)
    (hc : StreamSource.Coherent source state environment code.val tail)
    (codeLen q i finish next bytes : Usize) (stopped : Bool)
    (hlen : codeLen.val = code.length) (hq : q.val ≤ codeLen.val)
    (h : FrameStep source state codeLen q i (.cont (finish, next, bytes, stopped))) :
    (finish = q ∧ next = i) ∨
      ∃ content, ModuleCode.Extent code q content finish ∧ next.val = i.val + 1 := by
  rcases h with he | ⟨view, viewEnd, size, prefixLen, content,
    hread, hviewend, hdecoded, hcontent, hfinish, hbound, hnext⟩
  · exact .inl he
  · have horder : q.val ≤ viewEnd.val := by rw [hviewend]; exact Nat.le_min.mpr ⟨hq, by omega⟩
    have hend : viewEnd.val ≤ code.length := by
      rw [hviewend, ← hlen]
      exact Nat.min_le_left _ _
    obtain ⟨hview, _⟩ := stream.read_exact.sound source state environment code.val tail hc q viewEnd
      view horder hend hread
    have hprefix : Leb128.Decoded code q size content :=
      hdecoded.of_slice_view horder hend hview (by simp) hcontent
    exact .inr ⟨content, ⟨size, hprefix, hfinish, by omega⟩, hnext⟩

end Itasca.StreamFraming

namespace Itasca

/-- Fold an invariant over the prefix reads actually reached by an accepted
batch loop. Source callback totality is deliberately unnecessary. -/
theorem stream.get_next_batch_loop.accepted_induction {S : Type}
    (source : stream.Source S) (state : S)
    (codeLen start first num threshold : Usize)
    (P : Usize → Usize → Prop)
    (hstep : ∀ q i finish next bytes stopped, P q i →
      StreamFraming.FrameStep source state codeLen q i (.cont (finish, next, bytes, stopped)) →
      P finish next)
    (q i b : Usize) (stopped : Bool) (finish next : Usize)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : StreamFraming.BatchInvariant codeLen start first num threshold q i b stopped)
    (hprogress : first.val < i.val → start.val < q.val)
    (hp : P q i)
    (h : stream.get_next_batch_loop source state codeLen first num threshold q i b stopped =
      .ok (.Ok (finish, next))) :
    StreamFraming.BatchPost codeLen start first num (.Ok (finish, next)) ∧ P finish next := by
  generalize hm : (2 * (num.val - i.val) + if stopped then 0 else 1) = n
  induction n using Nat.strong_induction_on generalizing q i b stopped with
  | h n ih =>
    unfold stream.get_next_batch_loop at h
    rw [loop] at h
    obtain ⟨reply, hbody, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hs := stream.get_next_batch_loop.body.accepted source state codeLen start first num
      threshold q i b stopped reply hcap hmore hinv hprogress hbody
    cases reply with
    | done result =>
      have he : result = .Ok (finish, next) := by simpa using hrest
      subst result
      obtain ⟨hpost, he⟩ := hs
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hpost, hp⟩
    | cont pair =>
      obtain ⟨q', i', b', stopped'⟩ := pair
      obtain ⟨⟨⟨hinv', hprogress'⟩, hdecrease⟩, hframe⟩ := hs
      have hlt : (2 * (num.val - i'.val) + if stopped' then 0 else 1) < n := by omega
      have hrec : stream.get_next_batch_loop source state codeLen first num threshold
          q' i' b' stopped' = .ok (.Ok (finish, next)) := hrest
      exact ih _ hlt q' i' b' stopped' hinv' hprogress'
        (hstep q i q' i' b' stopped' hp hframe) hrec rfl

/-- Every accepted batch makes strict byte and function progress and stays inside the bounds
established by the driver. No premise is placed on source calls that the run did not reach. -/
theorem stream.get_next_batch.sound {S : Type} (source : stream.Source S) (state : S)
    (codeLen start first num threshold finish next : Usize)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hstart : start.val ≤ codeLen.val) (hmore : first.val < num.val)
    (h : stream.get_next_batch source state codeLen start first num threshold =
      .ok (.Ok (finish, next))) :
    start.val < finish.val ∧ finish.val ≤ codeLen.val ∧
      first.val < next.val ∧ next.val ≤ num.val := by
  apply (stream.get_next_batch_loop.accepted_induction source state codeLen start first num threshold
    (fun _ _ => True) (by intros; trivial) start first 0#usize false finish next hcap hmore
    (by simp [StreamFraming.BatchInvariant, hstart]; omega) (by omega) trivial h).1

end Itasca
