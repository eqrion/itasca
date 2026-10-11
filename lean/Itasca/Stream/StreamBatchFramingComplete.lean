import Itasca.Stream.StreamBatchSound
import Itasca.Module.ModuleCodeLimits

open Aeneas Aeneas.Std

namespace Itasca.StreamSource

/-- Available immutable views determine every successful source observation. -/
theorem Available.coherent {S : Type} {source : stream.Source S} {state : S}
    {environment code tail : List U8} (h : Available source state environment code tail) :
    Coherent source state environment code tail := by
  constructor
  · intro bytes hr
    obtain ⟨expected, he, hv⟩ := h.environment_read
    have heq : bytes = expected := by simpa [hr] using he
    simpa [heq] using hv
  · intro len hr
    obtain ⟨expected, he, hv⟩ := h.code_len_read
    have heq : len = expected := by simpa [hr] using he
    simpa [heq] using hv
  · intro first last bytes ho hb hr
    obtain ⟨expected, he, hv⟩ := h.code_read first last ho hb
    have heq : bytes = expected := by simpa [hr] using he
    simpa [heq] using hv
  · intro bytes hr
    obtain ⟨expected, he, hv⟩ := h.tail_read
    have heq : bytes = expected := by simpa [hr] using he
    simpa [heq] using hv

end Itasca.StreamSource

namespace Itasca

private theorem batch_prefix_read {S : Type} (source : stream.Source S) (state : S)
    (environment tail : List U8) (code : Slice U8)
    (ha : StreamSource.Available source state environment code.val tail)
    (codeLen q content finish : Usize) (hlen : codeLen.val = code.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hext : ModuleCode.Extent code q content finish) :
    ∃ (need : Usize) (view : Slice U8) (len prefixLen : Usize),
      (q + limits.MAX_LEB_BYTES : Result Usize) = .ok need ∧
      stream.read_exact source state q (core.cmp.impls.OrdUsize.min codeLen need) = .ok (.Ok view) ∧
      stream.read_len view 0#usize = .ok (.Ok (len, prefixLen)) ∧
      limits.add_offset q prefixLen = .ok (.Ok content) ∧
      limits.add_offset content len = .ok (.Ok finish) ∧
      finish.val = content.val + len.val := by
  obtain ⟨size, hd, hfinish, hbound⟩ := hext
  have hspan := hd.span
  have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
    have := ModuleCode.module_room
    simp only [limits.MAX_LEB_BYTES]
    scalar_tac
  obtain ⟨need, hneed, hneedval⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := q) (y := limits.MAX_LEB_BYTES) (by scalar_tac))
  let viewEnd := core.cmp.impls.OrdUsize.min codeLen need
  have hvend : viewEnd.val = Nat.min codeLen.val (q.val + 5) := by
    simp [viewEnd, hneedval, limits.MAX_LEB_BYTES]
  have ho : q.val ≤ viewEnd.val := by
    rw [hvend]; apply Nat.le_min.mpr; constructor <;> omega
  have hb : viewEnd.val ≤ code.length := by rw [hvend, ← hlen]; exact Nat.min_le_left _ _
  have hw : content.val ≤ viewEnd.val := by
    rw [hvend]; apply Nat.le_min.mpr; constructor <;> omega
  obtain ⟨view, hread, hview⟩ := ha.code_read q viewEnd ho hb
  have hvlen : view.length = viewEnd.val - q.val := by
    change view.val.length = _
    rw [hview, List.slice_length]
    apply Nat.min_eq_right
    change viewEnd.val - q.val ≤ code.length - q.val
    omega
  have hexact := stream.read_exact.complete source state q viewEnd view ho hread hvlen
  obtain ⟨prefixLen, hprefix, hpval⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := content) (y := q) (by scalar_tac))
  have hp : content.val = q.val + prefixLen.val := by omega
  have hdview : Leb128.Decoded view 0#usize size prefixLen :=
    hd.to_slice_view ho hb hview (by simp) hp hw
  obtain ⟨len, hlenread, hlenval⟩ := stream.read_len.complete view 0#usize prefixLen size hdview
  obtain ⟨content', hc, hcval⟩ := limits.add_offset.complete q prefixLen (by omega)
  have heqc : content' = content := by apply UScalar.eq_of_val_eq; omega
  subst content'
  obtain ⟨finish', hf, hfval⟩ := limits.add_offset.complete content len (by omega)
  have heqf : finish' = finish := by apply UScalar.eq_of_val_eq; omega
  subst finish'
  exact ⟨need, view, len, prefixLen, hneed, hexact, hlenread, hc, hf, by omega⟩

/-- An independently framed next entry prevents every Rust error branch of
the batching body. The threshold may be zero and never counts size-prefix bytes. -/
theorem stream.get_next_batch_loop.body.complete_spec {S : Type}
    (source : stream.Source S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : StreamSource.Available source state environment code.val tail)
    (codeLen start first num threshold q i b : Usize) (stopped : Bool)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamFraming.BatchInvariant codeLen start first num threshold q i b stopped)
    (hentry : i.val < num.val → stopped = false →
      ∃ content finish, ModuleCode.Extent code q content finish) :
    stream.get_next_batch_loop.body source state codeLen first num threshold q i b stopped ⦃ r =>
      match r with | .done (.Err _) => False | _ => True ⦄ := by
  obtain ⟨hstart, hq, hfirst, hi, hb, hinitial, hbudget⟩ := hinv
  unfold stream.get_next_batch_loop.body
  split
  · rename_i himore
    split
    · simp
    · rename_i hstop
      have hfalse : stopped = false := by cases stopped <;> simp_all
      obtain ⟨content, finish, hext⟩ := hentry (by exact himore) hfalse
      have hspan := hext.span
      obtain ⟨need, view, len, prefixLen, hneed, hread, hlenread, hc, hf, hend⟩ :=
        batch_prefix_read source state environment tail code ha codeLen q content finish hlen hcap hext
      have hfbound : ¬ finish > codeLen := by scalar_tac
      have hbroom : b.val + len.val ≤ Usize.max := by scalar_tac
      have hiroom : i.val + 1 ≤ Usize.max := by scalar_tac
      simp only [hneed, bind_ok, lift, hread, core.result.Result.Insts.CoreOpsTry.branch,
        hlenread]
      split
      · rename_i hne
        have hne' : i ≠ first := by simpa using hne
        have hbudget := hbudget hfalse hne'
        step
        split
        · simp
        · simp only [hc, hf, bind_ok, hfbound, ↓reduceIte]
          step*
      · simp [hc, hf]
        step*
  · simp

open ModuleBinary

/-- Successful batching preserves the independently encoded list as an exact
nonempty prefix and remaining suffix. Any stronger entry-encoding relation is
retained, so the worker's body/local limits are not lost during framing. -/
theorem stream.get_next_batch.complete_spec {S : Type}
    (source : stream.Source S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : StreamSource.Available source state environment code.val tail)
    (R : Code → List U8 → Prop) (hencoding : ∀ entry bytes, R entry bytes → CodeEncoding entry bytes)
    (codeLen start first num threshold : Usize) (entries : List Code)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val) (hcount : first.val + entries.length = num.val)
    (hbytes : At (Rep R) code start entries codeLen) :
    stream.get_next_batch source state codeLen start first num threshold ⦃ r =>
      ∃ finish next taken rest, r = .Ok (finish, next) ∧
        StreamFraming.BatchPost codeLen start first num (.Ok (finish, next)) ∧
        entries = taken ++ rest ∧ taken ≠ [] ∧
        next.val = first.val + taken.length ∧ num.val = next.val + rest.length ∧
        At (Rep R) code start taken finish ∧ At (Rep R) code finish rest codeLen ⦄ := by
  have hextent {q finish : Usize} {entry : Code} (h : At R code q entry finish) :
      ∃ content, ModuleCode.Extent code q content finish := by
    obtain ⟨bytes, he, hs⟩ := h
    exact (show At CodeEncoding code q entry finish from ⟨bytes, hencoding entry bytes he, hs⟩).code_extent
  unfold stream.get_next_batch stream.get_next_batch_loop
  apply loop.spec_decr_nat
    (fun s => 2 * (num.val - s.2.1.val) + if s.2.2.2 then 0 else 1)
    (fun s =>
      StreamFraming.BatchInvariant codeLen start first num threshold s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
      (first.val < s.2.1.val → start.val < s.1.val) ∧
      ∃ taken rest, entries = taken ++ rest ∧ s.2.1.val = first.val + taken.length ∧
        num.val = s.2.1.val + rest.length ∧ At (Rep R) code start taken s.1 ∧
        At (Rep R) code s.1 rest codeLen)
  · rintro ⟨q, i, b, stopped⟩ ⟨hinv, hprogress, taken, rest, heq, hntaken, hnrest, htaken, hrest⟩
    dsimp only
    dsimp only at hinv hprogress hntaken hnrest htaken hrest
    have hreturn : i.val < num.val → stopped = false → ∀ last : Usize,
        last.val = Nat.min codeLen.val (q.val + 5) → ∃ r, source.code state q last = .ok r := by
      intro _ _ last hlast
      have ho : q.val ≤ last.val := by
        rw [hlast]; exact Nat.le_min.mpr ⟨hinv.2.1, by omega⟩
      have hb : last.val ≤ code.length := by rw [hlast, ← hlen]; exact Nat.min_le_left _ _
      obtain ⟨view, hv, _⟩ := ha.code_read q last ho hb
      exact ⟨.Ok view, hv⟩
    obtain ⟨reply, hbody, hp⟩ := WP.spec_imp_exists
      (stream.get_next_batch_loop.body.spec source state codeLen start first num threshold
        q i b stopped hcap hmore hinv hprogress hreturn)
    have hentry : i.val < num.val → stopped = false →
        ∃ content finish, ModuleCode.Extent code q content finish := by
      intro hi _
      cases rest with
      | nil => simp only [List.length_nil] at hnrest; omega
      | cons entry rest =>
        obtain ⟨middle, he, _⟩ := hrest.rep_cons
        obtain ⟨content, hc⟩ := hextent he
        exact ⟨content, middle, hc⟩
    have hgood := stream.get_next_batch_loop.body.complete_spec source state environment tail code ha
      codeLen start first num threshold q i b stopped hlen hcap hinv hentry
    simp only [hbody, WP.spec_ok] at hgood
    rw [hbody]
    simp only [WP.spec_ok]
    cases reply with
    | done result =>
      cases result with
      | Err e => exact False.elim hgood
      | Ok pair =>
        obtain ⟨finish, next⟩ := pair
        obtain ⟨hpost, he⟩ := hp
        obtain ⟨hfinish, hnext⟩ := he
        subst finish
        subst next
        refine ⟨q, i, taken, rest, rfl, hpost, heq, ?_, hntaken, hnrest, htaken, hrest⟩
        intro hz
        have hlt := hpost.2.2.1
        simp only [hz, List.length_nil] at hntaken
        omega
    | cont pair =>
      obtain ⟨q', i', b', stopped'⟩ := pair
      dsimp only at *
      obtain ⟨⟨⟨hinv', hprogress'⟩, hdecrease⟩, hframe⟩ := hp
      refine ⟨⟨hinv', hprogress', ?_⟩, hdecrease⟩
      rcases StreamFraming.FrameStep.extent source state environment tail code ha.coherent
        codeLen q i q' i' b' stopped' hlen hinv.2.1 hframe with
        ⟨rfl, rfl⟩ | ⟨content, hframe, hnext⟩
      · exact ⟨taken, rest, heq, hntaken, hnrest, htaken, hrest⟩
      · have hi : i.val < num.val := by have := hinv'.2.2.2.1; omega
        cases rest with
        | nil => simp only [List.length_nil] at hnrest; omega
        | cons entry rest =>
          obtain ⟨middle, he, hr⟩ := hrest.rep_cons
          obtain ⟨entryContent, hext⟩ := hextent he
          obtain ⟨size, hd, hend, _⟩ := hframe
          obtain ⟨size', hd', hend', _⟩ := hext
          obtain ⟨hsize, hcontent⟩ := ModuleCode.decoded_unique hd hd'
          have hmiddle : middle = q' := by apply UScalar.eq_of_val_eq; rw [hend, hend', ← hcontent, ← hsize]
          subst middle
          refine ⟨taken ++ [entry], rest, ?_, ?_, ?_, htaken.rep_snoc he, hr⟩
          · simpa [List.append_assoc] using heq
          · simp only [List.length_append, List.length_singleton]; omega
          · simp only [List.length_cons] at hnrest; omega
  · have hstart : start.val ≤ codeLen.val := hbytes.span.1
    dsimp only
    refine ⟨?_, by omega, [], entries, by simp, by simp, hcount.symm, ?_, hbytes⟩
    · simp [StreamFraming.BatchInvariant, hstart]
      omega
    · exact ⟨[], .nil, Wasm.BytesAt.nil code start (by omega)⟩

/-- Independent bounded entry encodings force an actual successful batch,
retaining precisely the nonempty encoded prefix and its unconsumed suffix. -/
theorem stream.get_next_batch.complete {S : Type}
    (source : stream.Source S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : StreamSource.Available source state environment code.val tail)
    (codeLen start first num threshold : Usize) (entries : List Code)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val) (hcount : first.val + entries.length = num.val)
    (hbytes : At (Rep CodeEncodingWithinLimits) code start entries codeLen) :
    ∃ finish next taken rest,
      stream.get_next_batch source state codeLen start first num threshold = .ok (.Ok (finish, next)) ∧
      StreamFraming.BatchPost codeLen start first num (.Ok (finish, next)) ∧
      entries = taken ++ rest ∧ taken ≠ [] ∧
      next.val = first.val + taken.length ∧ num.val = next.val + rest.length ∧
      At (Rep CodeEncodingWithinLimits) code start taken finish ∧
      At (Rep CodeEncodingWithinLimits) code finish rest codeLen := by
  obtain ⟨r, hr, finish, next, taken, rest, rfl, hp⟩ := WP.spec_imp_exists
    (stream.get_next_batch.complete_spec source state environment tail code ha CodeEncodingWithinLimits
      (fun _ _ h => h.encoding) codeLen start first num threshold entries hlen hcap hmore hcount hbytes)
  exact ⟨finish, next, taken, rest, hr, hp⟩

/-- An available exact source view carries precisely the independently
encoded entries in the corresponding interval of the logical code region. -/
theorem stream.read_exact.complete_rep {S A : Type}
    (source : stream.Source S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : StreamSource.Available source state environment code.val tail)
    (R : A → List U8 → Prop) (start finish : Usize) (entries : List A)
    (hbytes : At (Rep R) code start entries finish) :
    ∃ view, stream.read_exact source state start finish = .ok (.Ok view) ∧
      Wasm.BytesAt code start view.val finish ∧ Rep R entries view.val := by
  obtain ⟨bytes, hrep, hspan⟩ := hbytes
  have ho : start.val ≤ finish.val := by have := hspan.length; omega
  obtain ⟨view, hread, hview⟩ := ha.code_read start finish ho hspan.bound
  have hvlen : view.length = finish.val - start.val := by
    change view.val.length = _
    rw [hview, List.slice_length]
    apply Nat.min_eq_right
    change finish.val - start.val ≤ code.length - start.val
    have := hspan.bound
    omega
  have hvspan := Wasm.BytesAt.of_slice_view ho hspan.bound hview
  have heq : bytes = view.val := List.append_cancel_right (hspan.suffix.symm.trans hvspan.suffix)
  exact ⟨view, stream.read_exact.complete source state start finish view ho hread hvlen,
    hvspan, heq ▸ hrep⟩

/-- Batching and its following exact read produce the worker's complete byte
view, with bounded entry encodings and function counts preserved. -/
theorem stream.get_next_batch.complete_view {S : Type}
    (source : stream.Source S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : StreamSource.Available source state environment code.val tail)
    (codeLen start first num threshold : Usize) (entries : List Code)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val) (hcount : first.val + entries.length = num.val)
    (hbytes : At (Rep CodeEncodingWithinLimits) code start entries codeLen) :
    ∃ finish next taken rest view,
      stream.get_next_batch source state codeLen start first num threshold = .ok (.Ok (finish, next)) ∧
      StreamFraming.BatchPost codeLen start first num (.Ok (finish, next)) ∧
      entries = taken ++ rest ∧ taken ≠ [] ∧
      next.val = first.val + taken.length ∧ num.val = next.val + rest.length ∧
      At (Rep CodeEncodingWithinLimits) code start taken finish ∧
      At (Rep CodeEncodingWithinLimits) code finish rest codeLen ∧
      stream.read_exact source state start finish = .ok (.Ok view) ∧
      Wasm.BytesAt code start view.val finish ∧ Rep CodeEncodingWithinLimits taken view.val := by
  obtain ⟨finish, next, taken, rest, hrun, hp, heq, hne, hn, hr, htaken, hrest⟩ :=
    stream.get_next_batch.complete source state environment tail code ha codeLen start first num threshold
      entries hlen hcap hmore hcount hbytes
  obtain ⟨view, hread, hview, hrep⟩ := stream.read_exact.complete_rep source state environment tail code ha
    CodeEncodingWithinLimits start finish taken htaken
  exact ⟨finish, next, taken, rest, view, hrun, hp, heq, hne, hn, hr, htaken, hrest, hread, hview, hrep⟩

end Itasca
