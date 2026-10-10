import Itasca.StreamBatchSteps

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- Consecutive declared entry extents in the logical code region. This
certifies framing alone; it makes no claim about locals or instruction typing. -/
inductive EntryFrames (data : Slice U8) (start : Usize) : Usize → Nat → Prop where
  | nil : start.val ≤ data.length → EntryFrames data start start 0
  | snoc {pos content finish count} : EntryFrames data start pos count →
      ModuleCode.Extent data pos content finish → EntryFrames data start finish (count + 1)

theorem EntryFrames.span {data start finish count}
    (h : EntryFrames data start finish count) :
    start.val ≤ finish.val ∧ finish.val ≤ data.length ∧ count ≤ finish.val - start.val := by
  induction h with
  | nil hbound => simp [hbound]
  | snoc _ hext ih => have := hext.span; omega

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
    obtain ⟨reply, hbody, hrest⟩ := VisitorErasure.bind_ok_inv _ _ _ h
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

/-- Every accepted batch makes strict byte and function progress and stays
inside the driver-established bounds, even if other source callbacks diverge. -/
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

/-- Accepted batching frames exactly the returned number of consecutive
entries in the coherent code region. Body validation remains a separate step. -/
theorem stream.get_next_batch.frames {S : Type} (source : stream.Source S) (state : S)
    (environment tail : List U8) (code : Slice U8)
    (hc : StreamSource.Coherent source state environment code.val tail)
    (codeLen start first num threshold finish next : Usize)
    (hlen : codeLen.val = code.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hstart : start.val ≤ codeLen.val) (hmore : first.val < num.val)
    (h : stream.get_next_batch source state codeLen start first num threshold =
      .ok (.Ok (finish, next))) :
    (start.val < finish.val ∧ finish.val ≤ codeLen.val ∧
      first.val < next.val ∧ next.val ≤ num.val) ∧
      StreamFraming.EntryFrames code start finish (next.val - first.val) := by
  let P (q i : Usize) := first.val ≤ i.val ∧
    StreamFraming.EntryFrames code start q (i.val - first.val)
  have hstep : ∀ q i finish next bytes stopped, P q i →
      StreamFraming.FrameStep source state codeLen q i (.cont (finish, next, bytes, stopped)) →
      P finish next := by
    intro q i finish next bytes stopped hp hf
    obtain ⟨hfirst, hframes⟩ := hp
    rcases StreamFraming.FrameStep.extent source state environment tail code hc
      codeLen q i finish next bytes stopped hlen (by have := hframes.span; omega) hf with
      ⟨rfl, rfl⟩ | ⟨content, hext, hnext⟩
    · exact ⟨hfirst, hframes⟩
    · have hn : next.val - first.val = (i.val - first.val) + 1 := by omega
      exact ⟨by omega, hn ▸ hframes.snoc hext⟩
  have hs := stream.get_next_batch_loop.accepted_induction source state codeLen start first num threshold
    P hstep start first 0#usize false finish next hcap hmore
    (by simp [StreamFraming.BatchInvariant, hstart]; omega) (by omega)
    ⟨by omega, by simpa using StreamFraming.EntryFrames.nil (data := code) (by omega : start.val ≤ code.length)⟩ h
  exact ⟨hs.1, hs.2.2⟩

end Itasca
