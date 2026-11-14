import Itasca.Support.Result
import Itasca.Stream.SplitTotal
import Itasca.Stream.Header

/-!
Sections, each formerly its own module: FramingStep, FramingSound, Partition, SubmissionSound.
-/

/-! ## FramingStep -/

section

/-!
# Single framing step

Specification of one iteration, `stream.get_next_batch_loop.body`, of the batch framing loop.
`StreamFraming.BatchStepPost` combines the arithmetic invariant with `StreamFraming.FrameStep`,
which records the actual view read, the decoded entry size and the consecutive entry boundaries.
`stream.get_next_batch_loop.body.accepted` derives the step facts from an ordinary return of the
body, so no premise is placed on source calls that were not reached.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- A continuing framing step either does not take another entry, or
records the exact returned view, decoded length and consecutive boundaries. -/
def FrameStep {S : Type} (source : stream.Source S) (state : S) (codeLen q i : Usize) :
    ControlFlow (Usize × Usize × Usize × Bool)
      (core.result.Result (Usize × Usize) error.Error) → Prop
  | .done (.Ok (finish, next)) => finish = q ∧ next = i
  | .done (.Err _) => True
  | .cont (finish, next, _, _) =>
      (finish = q ∧ next = i) ∨
        ∃ (view : Slice U8) (viewEnd : Usize) (size : U32) (prefixLen content : Usize),
          stream.read_exact source state q viewEnd = .ok (.Ok view) ∧
          viewEnd.val = Nat.min codeLen.val (q.val + 5) ∧
          Leb128.Decoded view 0#usize size prefixLen ∧
          content.val = q.val + prefixLen.val ∧
          finish.val = content.val + size.val ∧
          finish.val ≤ codeLen.val ∧ next.val = i.val + 1

/-- Arithmetic preservation and the observed extent of one extracted step. -/
def BatchStepPost {S : Type} (source : stream.Source S) (state : S)
    (codeLen start first num threshold q i : Usize) (stopped : Bool)
    (r : ControlFlow (Usize × Usize × Usize × Bool)
      (core.result.Result (Usize × Usize) error.Error)) : Prop :=
  (match r with
   | .done result => BatchPost codeLen start first num result
   | .cont (q', i', b', stopped') =>
       (BatchInvariant codeLen start first num threshold q' i' b' stopped' ∧
         (first.val < i'.val → start.val < q'.val)) ∧
         (2 * (num.val - i'.val) + if stopped' then 0 else 1) <
           (2 * (num.val - i.val) + if stopped then 0 else 1)) ∧
  FrameStep source state codeLen q i r

private theorem advance {codeLen start first num threshold q i b finish j new : Usize}
    {prefixLen len : Nat}
    (hstart : start.val ≤ q.val) (hfirst : first.val ≤ i.val)
    (himore : i.val < num.val) (hb : b.val ≤ q.val - start.val)
    (hprefix : 0 < prefixLen) (hend : finish.val = q.val + prefixLen + len)
    (hbound : finish.val ≤ codeLen.val) (hcount : j.val = i.val + 1)
    (hbytes : new.val = b.val + len) :
    (BatchInvariant codeLen start first num threshold finish j new (decide (new ≥ threshold)) ∧
      (first.val < j.val → start.val < finish.val)) ∧
      (2 * (num.val - j.val) + if decide (new ≥ threshold) then 0 else 1) <
        2 * (num.val - i.val) + 1 := by
  have hj : first.val < j.val := by omega
  have hne : j ≠ first := by intro he; have := congrArg UScalar.val he; omega
  refine ⟨⟨⟨by omega, hbound, by omega, by omega, by omega, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro he; exact False.elim (hne he)
  · intro hz _
    have : ¬ new.val ≥ threshold.val := by simpa using hz
    omega
  · intro _; omega
  · split <;> omega

end Itasca.StreamFraming

namespace Itasca

/-- The extracted loop body preserves the arithmetic invariant and records each consumed declared
extent, under a return premise only for the code read it reaches. -/
theorem stream.get_next_batch_loop.body.spec {S : Type} (source : stream.Source S) (state : S)
    (codeLen start first num threshold q i b : Usize) (stopped : Bool)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : StreamFraming.BatchInvariant codeLen start first num threshold q i b stopped)
    (hprogress : first.val < i.val → start.val < q.val)
    (hreturn : i.val < num.val → stopped = false → ∀ last,
      last.val = Nat.min codeLen.val (q.val + 5) → ∃ r, source.code state q last = .ok r) :
    stream.get_next_batch_loop.body source state codeLen first num threshold q i b stopped ⦃ r =>
      (match r with
       | .done result => StreamFraming.BatchPost codeLen start first num result
       | .cont (q', i', b', stopped') =>
           (StreamFraming.BatchInvariant codeLen start first num threshold q' i' b' stopped' ∧
             (first.val < i'.val → start.val < q'.val)) ∧
             (2 * (num.val - i'.val) + if stopped' then 0 else 1) <
               (2 * (num.val - i.val) + if stopped then 0 else 1)) ∧
      StreamFraming.FrameStep source state codeLen q i r ⦄ := by
  obtain ⟨hstart, hq, hfirst, hi, hb, hinitial, hbudget⟩ := hinv
  unfold stream.get_next_batch_loop.body
  try dsimp only
  split
  · rename_i himore
    split
    · rename_i hstop
      have hne : i ≠ first := by intro he; have := (hinitial he).2.2; simp_all
      have hlt : first.val < i.val := by
        have : first.val ≠ i.val := by intro he; apply hne; exact UScalar.eq_of_val_eq he.symm
        omega
      simpa [StreamFraming.BatchPost, StreamFraming.FrameStep] using
        ⟨hprogress hlt, hq, hlt, hi⟩
    · rename_i hnotstop
      have hfalse : stopped = false := by cases stopped <;> simp_all
      have hiroom : i.val + 1 ≤ Usize.max := by scalar_tac
      have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
        have := ModuleCode.module_room
        simp only [limits.MAX_LEB_BYTES]
        scalar_tac
      obtain ⟨need, hneed, hneedval⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := q) (y := limits.MAX_LEB_BYTES) (by scalar_tac))
      rw [hneed]
      simp only [bind_ok, lift]
      have hviewend : (core.cmp.impls.OrdUsize.min codeLen need).val =
          Nat.min codeLen.val (q.val + 5) := by
        rw [StreamFraming.min_val, hneedval]
        simp [limits.MAX_LEB_BYTES]
      have horder : q.val ≤ (core.cmp.impls.OrdUsize.min codeLen need).val := by
        rw [hviewend]
        exact Nat.le_min.mpr ⟨hq, by omega⟩
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_exact.spec source state q
        (core.cmp.impls.OrdUsize.min codeLen need) horder (hreturn (by exact himore) hfalse _ hviewend))
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost, StreamFraming.FrameStep]
      | Ok view =>
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨r, hl, hlp⟩ := WP.spec_imp_exists (stream.read_len.spec view 0#usize)
        rw [hl]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost, StreamFraming.FrameStep]
        | Ok pair =>
          obtain ⟨len, prefixLen⟩ := pair
          obtain ⟨size, hlen, hdecoded⟩ := hlp
          have hprefix := hdecoded.span
          have hprefixpos : 0 < prefixLen.val := by simpa using hprefix.1
          simp
          split
          · rename_i hequal
            have heqi : i = first := UScalar.eq_of_val_eq hequal
            have hbzero : b = 0#usize := (hinitial heqi).2.1
            obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec q prefixLen)
            rw [hc]
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost, StreamFraming.FrameStep]
            | Ok content =>
              simp
              obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
              rw [hf]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost, StreamFraming.FrameStep]
              | Ok finish =>
                simp
                split
                · simp [StreamFraming.BatchPost, StreamFraming.FrameStep]
                · rename_i hfinish
                  have hfbound : finish.val ≤ codeLen.val := by scalar_tac
                  have hbroom : b.val + len.val ≤ Usize.max := by
                    simp only [hbzero]
                    scalar_tac
                  step
                  step
                  have ha := StreamFraming.advance (num := num) (threshold := threshold)
                    (j := func1) (new := batch_bytes1) (len := len.val)
                    hstart hfirst (by exact himore) hb hprefixpos
                    (by have := hcp.1; have := hfp.1; omega) hfbound
                    func1_post batch_bytes1_post
                  refine ⟨ha.1.1, ha.1.2, ?_, ?_⟩
                  · simpa using ha.2
                  · exact .inr ⟨view, core.cmp.impls.OrdUsize.min codeLen need, size, prefixLen,
                      content, hr, hviewend, hdecoded, hcp.1, by have := hfp.1; omega,
                      hfbound, func1_post⟩
          · rename_i hnotequal
            have hne : i ≠ first := by intro he; simp [he] at hnotequal
            have hbbound := hbudget hfalse hne
            step
            split
            · simp only [WP.spec_ok, StreamFraming.BatchInvariant]
              constructor
              · refine ⟨⟨hstart, hq, hfirst, hi, hb, ?_, ?_⟩, hprogress, ?_⟩
                · intro he; exact False.elim (hne he)
                · intro he; cases he
                · simp
              · exact .inl ⟨rfl, rfl⟩
            · obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec q prefixLen)
              rw [hc]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost, StreamFraming.FrameStep]
              | Ok content =>
                simp
                obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
                rw [hf]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost, StreamFraming.FrameStep]
                | Ok finish =>
                  simp
                  split
                  · simp [StreamFraming.BatchPost, StreamFraming.FrameStep]
                  · rename_i hfinish
                    have hfbound : finish.val ≤ codeLen.val := by scalar_tac
                    have hbroom : b.val + len.val ≤ Usize.max := by
                      have hfmax := hfp.2
                      have := ModuleCode.module_room
                      scalar_tac
                    step
                    step
                    have ha := StreamFraming.advance (num := num) (threshold := threshold)
                      (j := func1) (new := batch_bytes1) (len := len.val)
                      hstart hfirst (by exact himore) hb hprefixpos
                      (by have := hcp.1; have := hfp.1; omega) hfbound
                      func1_post batch_bytes1_post
                    refine ⟨ha.1.1, ha.1.2, ?_, ?_⟩
                    · simpa using ha.2
                    · exact .inr ⟨view, core.cmp.impls.OrdUsize.min codeLen need, size, prefixLen,
                        content, hr, hviewend, hdecoded, hcp.1, by have := hfp.1; omega,
                        hfbound, func1_post⟩
  · rename_i hstop
    have hdone : i.val = num.val := by scalar_tac
    simpa [StreamFraming.BatchPost, StreamFraming.FrameStep] using
      ⟨hprogress (by omega), hq, (by omega : first.val < i.val), hi⟩

/-- An ordinary return of the loop body reveals the reached source callback;
no return assumption is imposed on any unexecuted source operation. -/
theorem stream.get_next_batch_loop.body.accepted {S : Type}
    (source : stream.Source S) (state : S)
    (codeLen start first num threshold q i b : Usize) (stopped : Bool)
    (reply : ControlFlow (Usize × Usize × Usize × Bool)
      (core.result.Result (Usize × Usize) error.Error))
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : StreamFraming.BatchInvariant codeLen start first num threshold q i b stopped)
    (hprogress : first.val < i.val → start.val < q.val)
    (h : stream.get_next_batch_loop.body source state codeLen first num threshold q i b stopped =
      .ok reply) :
    StreamFraming.BatchStepPost source state codeLen start first num threshold q i stopped reply := by
  have hreturn : i.val < num.val → stopped = false → ∀ last : Usize,
      last.val = Nat.min codeLen.val (q.val + 5) → ∃ r, source.code state q last = .ok r := by
    intro hi hstop last hlast
    have hr := h
    have hiless : i < num := by exact hi
    simp only [stream.get_next_batch_loop.body, hiless, hstop, Bool.false_eq_true,
      ↓reduceIte] at hr
    obtain ⟨need, hneed, hr⟩ := ResultFacts.bind_ok_inv _ _ _ hr
    have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
      have hq := hinv.2.1
      have := ModuleCode.module_room
      simp only [limits.MAX_LEB_BYTES]
      scalar_tac
    have hneedval := UScalar.add_spec (x := q) (y := limits.MAX_LEB_BYTES) (by scalar_tac)
    simp only [hneed, WP.spec_ok] at hneedval
    have hend : core.cmp.impls.OrdUsize.min codeLen need = last := by
      apply UScalar.eq_of_val_eq
      rw [StreamFraming.min_val, hneedval, hlast]
      simp [limits.MAX_LEB_BYTES]
    simp only [lift, bind_ok, hend] at hr
    obtain ⟨r, hread, _⟩ := ResultFacts.bind_ok_inv _ _ _ hr
    unfold stream.read_exact at hread
    obtain ⟨r, hsource, _⟩ := ResultFacts.bind_ok_inv _ _ _ hread
    exact ⟨r, hsource⟩
  have hs := stream.get_next_batch_loop.body.spec source state codeLen start first num threshold
    q i b stopped hcap hmore hinv hprogress hreturn
  simpa only [h, WP.spec_ok, StreamFraming.BatchStepPost] using hs

end Itasca

end

/-! ## FramingSound -/

section

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

end

/-! ## Partition -/

section

/-!
# Batch partitions

`StreamScheduler.Partition` records that a list of issued batches covers consecutive intervals of
the code region and consecutive defined-function indices, in submission order.
`StreamScheduler.Partition.encoding` and `StreamScheduler.Partition.code` assemble the per-batch
`StreamScheduler.Completed` certificates into one encoded and typed code section for the whole
module.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler
/-- Issued batches partition bytes and defined-function indices in submission
order. Worker completion order is deliberately absent from this relation. -/
inductive Partition (code : Slice U8) (env : metadata.Env) :
    Usize → Nat → List StreamBatch.Issued → Usize → Nat → Prop where
  | nil (pos : Usize) (func : Nat) : pos.val ≤ code.length →
      Partition code env pos func [] pos func
  | cons {pos func issued rest middle finish next} :
      issued.env = env → issued.code_offset = pos → issued.first_func.val = func →
      Wasm1.BytesAt code pos issued.code.val middle →
      Partition code env middle (func + issued.num_funcs.val) rest finish next →
      Partition code env pos func (issued :: rest) finish next

/-- Appending the next issued batch extends a partition. -/
theorem Partition.snoc {code env pos func history middle next issued finish}
    (h : Partition code env pos func history middle next)
    (henv : issued.env = env) (hoffset : issued.code_offset = middle)
    (hfunc : issued.first_func.val = next)
    (hbytes : Wasm1.BytesAt code middle issued.code.val finish) :
    Partition code env pos func (history ++ [issued]) finish (next + issued.num_funcs.val) := by
  induction h with
  | nil => exact .cons henv hoffset hfunc hbytes (.nil _ _ hbytes.bound)
  | cons he ho hf hb _ ih => exact .cons he ho hf hb (ih hoffset hfunc hbytes)

/-- Concatenates the entry certificates of completed batches in issuance order. The completion
premise is discharged by successful retirements. -/
theorem Partition.encoding {code env pos func history finish next}
    (h : Partition code env pos func history finish next)
    (hcompleted : ∀ issued ∈ history, Completed issued) :
    ∃ entries, next = func + entries.length ∧
      ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding)) code pos entries finish ∧
      ModuleCode.EntriesTyped env func entries := by
  induction h with
  | nil pos func hbound =>
    exact ⟨[], by simp, ⟨[], .nil, Wasm1.BytesAt.nil _ _ hbound⟩, .nil _⟩
  | @cons pos func issued rest middle finish next he ho hf hb hp ih =>
    obtain ⟨entries, hn, hr, ht⟩ := hcompleted issued (by simp)
    obtain ⟨restEntries, hnext, hrestBytes, hrestTyped⟩ := ih (fun issued hm => hcompleted issued (by simp [hm]))
    have hfirst : ModuleCode.EntriesTyped env func entries := by simpa [he, hf] using ht
    refine ⟨entries ++ restEntries, ?_, ModuleCode.entries_at_append ⟨issued.code.val, hr, hb⟩ hrestBytes,
      hfirst.append (by simpa [hn] using hrestTyped)⟩
    simp only [List.length_append]
    omega

/-- A checked header and a partition of the whole code region give the padded code section
encoding and the pairing of each declared function type with its typed code entry. -/
theorem Partition.code {code env entries history}
    (hheader : StreamFraming.HeaderAt code env entries)
    (h : Partition code env entries 0 history (Slice.len code) env.func_type_indices.val.length)
    (hcompleted : ∀ issued ∈ history, Completed issued) :
    ∃ codes, ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding (Profile.CodeEncoding)) [] codes code.val ∧
      List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes := by
  obtain ⟨codes, hn, hb, ht⟩ := h.encoding hcompleted
  have hcount : codes.length = env.func_type_indices.val.length := by omega
  have htyped := ht.forall₂ (by omega)
  rcases hheader with ⟨hbytes, _, hfuncs⟩ | ⟨count, hs, _⟩
  · have hcodes : codes = [] := by simpa [hfuncs] using hcount
    refine ⟨codes, ?_, by simpa using htyped⟩
    simp only [hcodes, hbytes]
    exact ⟨[], [], .nil, .absent, rfl⟩
  · obtain ⟨bytes, he, hspan⟩ := ModuleCode.Section.encoding hs hb hcount
    have heq : code.val = bytes := by simpa using hspan.suffix
    exact ⟨codes, ⟨[], code.val, .nil, heq ▸ he, rfl⟩, by simpa using htyped⟩

end Itasca.StreamScheduler

end

/-! ## SubmissionSound -/

section

/-!
# Submission soundness

Soundness of `stream.submit_code_batches` over a coherent source and a scheduler with
`StreamScheduler.Provenance`. `StreamSubmission.SoundInvariant` holds along the submission loop:
the issued batches partition the code region in order, batch IDs are numbered consecutively, the
pending IDs are distinct and bounded, and every issued batch is pending or completed.
`stream.submit_code_batches.sound` gives `StreamSubmission.SoundPost` for an accepted run.
Completed certificates arise only from successful retirements in the loop, never from a premise
on the scheduler. Unreached callbacks need not return.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSubmission
open StreamScheduler

/-- Invariant of a successful submission prefix: issued batches tile the code region in issuance
order, batch IDs are numbered consecutively, the pending IDs are distinct and bounded by the
capacity, and every issued batch is pending or has a completion certificate from a successful
retirement. -/
structure SoundInvariant (code : Slice U8) (env : metadata.Env) (start : Usize)
    (id : U64) (capacity : Usize) (history : List StreamBatch.Issued)
    (pending : alloc.vec.Vec Usize) (pos func nextId : Usize) : Prop where
  partition : Partition code env start 0 history pos func.val
  position : pos.val ≤ code.length
  functions : func.val ≤ env.func_type_indices.val.length
  next_id : nextId.val = history.length
  numbered : history.map (fun issued => issued.batch_id.val) = List.range history.length
  issued : ∀ issued ∈ history, issued.module_id = id ∧ issued.env = env ∧ issued.Bounded
  pending_history : ∀ batchId ∈ pending.val, ∃ issued ∈ history, issued.batch_id = batchId
  pending_distinct : pending.val.Nodup
  pending_bound : pending.length ≤ capacity.val
  accounted : ∀ issued ∈ history, issued.batch_id ∈ pending.val ∨ Completed issued

/-- The next batch ID differs from every issued batch ID. -/
theorem SoundInvariant.fresh {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant code env start id capacity history pending pos func nextId) :
    ∀ issued ∈ history, issued.batch_id ≠ nextId := by
  intro issued hm he
  have hb : issued.batch_id.val ∈ List.range history.length := by
    rw [← h.numbered]
    exact List.mem_map.mpr ⟨issued, hm, rfl⟩
  have hn := List.mem_range.mp hb
  rw [he, h.next_id] at hn
  omega

theorem SoundInvariant.pending_fresh {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant code env start id capacity history pending pos func nextId) :
    nextId ∉ pending.val := by
  intro hm
  obtain ⟨issued, hi, he⟩ := h.pending_history nextId hm
  exact h.fresh issued hi he

/-- The invariant holds before any batch is issued. -/
theorem SoundInvariant.initial (code : Slice U8) (env : metadata.Env) (start : Usize)
    (id : U64) (capacity : Usize) (hstart : start.val ≤ code.length) :
    SoundInvariant code env start id capacity [] (alloc.vec.Vec.new _) start 0#usize 0#usize := by
  constructor
  · exact .nil start 0 hstart
  · exact hstart
  · simp
  · simp
  · simp
  · simp
  · simp [alloc.vec.Vec.new]
  · simp [alloc.vec.Vec.new]
  · simp [alloc.vec.Vec.new]
  · simp

/-- Removing one pending ID yields a certificate only after a successful retirement. All other
outstanding and completed work stays accounted for. -/
theorem SoundInvariant.retire {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant code env start id capacity history pending pos func nextId)
    (remaining : alloc.vec.Vec Usize) (batchId : Usize)
    (hperm : (batchId :: remaining.val).Perm pending.val)
    (hcomplete : ∀ issued ∈ history, issued.module_id = id → issued.batch_id = batchId → Completed issued ) :
    SoundInvariant code env start id capacity history remaining pos func nextId := by
  have hnodup := hperm.nodup_iff.mpr h.pending_distinct
  rw [List.nodup_cons] at hnodup
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  refine ⟨h.partition, h.position, h.functions, h.next_id, h.numbered, h.issued,
    ?_, hnodup.2, ?_, ?_⟩
  · intro needle hm
    exact h.pending_history needle (hperm.mem_iff.mp (by simp [hm]))
  · change remaining.val.length ≤ _
    have hb := h.pending_bound
    change pending.val.length ≤ _ at hb
    omega
  · intro issued hi
    rcases h.accounted issued hi with hp | hc
    · have hm := hperm.mem_iff.mpr hp
      rcases List.mem_cons.mp hm with he | hr
      · exact .inr (hcomplete issued hi (h.issued issued hi).1 he)
      · exact .inl hr
    · exact .inr hc

/-- Issuing the next seed extends the byte and function tiling and the numbered issuance history.
The issued ID is pending and not yet completed. -/
theorem SoundInvariant.issue {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant code env start id capacity history pending pos func nextId)
    (issued : StreamBatch.Issued) (nextPending : alloc.vec.Vec Usize)
    (finish nextFunc nextBatchId : Usize)
    (hmodule : issued.module_id = id) (henv : issued.env = env)
    (hbatch : issued.batch_id = nextId) (hbounded : issued.Bounded)
    (hoffset : issued.code_offset = pos) (hfirst : issued.first_func = func)
    (hbytes : Wasm1.BytesAt code pos issued.code.val finish)
    (hcount : nextFunc.val = func.val + issued.num_funcs.val)
    (hfunctions : nextFunc.val ≤ env.func_type_indices.val.length)
    (hnext : nextBatchId.val = nextId.val + 1)
    (hpending : nextPending.val = pending.val ++ [nextId])
    (hroom : pending.length < capacity.val) :
    SoundInvariant code env start id capacity (history ++ [issued]) nextPending finish nextFunc nextBatchId := by
  refine ⟨?_, hbytes.bound, hfunctions, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcount]
    exact h.partition.snoc henv hoffset (by rw [hfirst]) hbytes
  · simp only [List.length_append, List.length_singleton]
    rw [hnext, h.next_id]
  · simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_singleton,
      h.numbered, List.range_succ]
    congr 1
    simp [hbatch, h.next_id]
  · intro old hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.issued old hm
    · have he : old = issued := by simpa using hm
      exact he ▸ ⟨hmodule, henv, hbounded⟩
  · intro needle hm
    rw [hpending] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨old, ho, he⟩ := h.pending_history needle hm
      exact ⟨old, List.mem_append_left _ ho, he⟩
    · have he : needle = nextId := by simpa using hm
      exact ⟨issued, by simp, by simpa [he] using hbatch⟩
  · rw [hpending, List.nodup_append]
    refine ⟨h.pending_distinct, by simp, ?_⟩
    intro a ha b hb
    have he : b = nextId := by simpa using hb
    subst b
    intro he
    exact h.pending_fresh (he ▸ ha)
  · change nextPending.val.length ≤ _
    rw [hpending, List.length_append, List.length_singleton]
    change pending.val.length < _ at hroom
    omega
  · intro old hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases h.accounted old hm with hp | hc
      · exact .inl (by rw [hpending]; simp [hp])
      · exact .inr hc
    · have he : old = issued := by simpa using hm
      subst old
      exact .inl (by rw [hbatch, hpending]; simp)

/-- Successful submission tiles the entire entry region and accounts for every issued ID as
pending or completed, with the scheduler tracking the resulting history. -/
def SoundPost {V : Type} (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.Env) (start : Usize) (id : U64) (capacity : Usize) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ history nextId,
      SoundInvariant code env start id capacity history pending (Slice.len code)
        (alloc.vec.Vec.len env.func_type_indices) nextId ∧ Tracks id history v
  | (.Err _, _) => True

private def BodyPost {V : Type} (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.Env) (start : Usize) (id : U64)
    (capacity func : Usize) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => SoundPost Tracks code env start id capacity result
  | .cont (v, pending, pos, next, batchId) => ∃ history,
      SoundInvariant code env start id capacity history pending pos next batchId ∧
      Tracks id history v ∧ func.val < next.val

end Itasca.StreamSubmission


namespace Itasca.StreamSubmission
private theorem resume_sound {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List StreamBatch.Issued)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : SoundInvariant code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v) (hfunc : func.val < env.func_type_indices.val.length)
    (hroom : pending.length < config.max_batches.val)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : (do
      let r ← stream.get_next_batch source state (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (finish, next) := val
        let r1 ← stream.read_exact source state pos finish
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue bytes =>
          let pending1 ← alloc.vec.Vec.push pending batchId
          let count ← next - func
          let (r2, v') ← visitor.submit_code_batch v
            { module_id := moduleId, batch_id := batchId, env := env, code := bytes,
              code_offset := pos, first_func := func, num_funcs := count,
              num_dispatched := 0#usize, dispatch_end := 0#usize,
              num_validated := 0#usize, validated_end := 0#usize, error := none }
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let nextId ← batchId + 1#usize
            Result.ok (ControlFlow.cont (v', pending1, finish, next, nextId))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
            Result.ok (ControlFlow.done (r3, v'))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
          Result.ok (ControlFlow.done (r2, v))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
        Result.ok (ControlFlow.done (r1, v))) = .ok out) :
    BodyPost Tracks code env start moduleId config.max_batches func out := by
  obtain ⟨r, hframe, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    subst out
    trivial
  | Ok pair =>
    obtain ⟨finish, next⟩ := pair
    obtain ⟨hprogress, hfinish, hnext, hnextbound⟩ := stream.get_next_batch.sound source state
      (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes finish next
      (by simpa using hcap) (by simpa using hinv.position) (by simpa using hfunc) hframe
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hread, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      subst out
      trivial
    | Ok bytes =>
      have hview := stream.read_exact.sound source state environment code.val tail hsource
        pos finish bytes (by omega) (by simpa using hfinish) hread
      have hspan := Wasm1.BytesAt.of_slice_view (by omega : pos.val ≤ finish.val)
        (by simpa using hfinish : finish.val ≤ code.length) hview.1
      simp at h
      obtain ⟨nextPending, hpush, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hpushspec := alloc.vec.Vec.push_spec pending batchId (by scalar_tac)
      rw [hpush] at hpushspec
      simp only [WP.spec_ok] at hpushspec
      obtain ⟨count, hsub, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hsubspec := UScalar.sub_equiv next func
      rw [hsub] at hsubspec
      let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count⟩
      have hissued : issued.Bounded := by
        dsimp [issued, StreamBatch.Issued.Bounded]
        have hlength := hspan.length
        change finish.val = pos.val + bytes.length at hlength
        have hbound := hspan.bound
        have hcountval := hsubspec.2.1
        have hnextbound' : next.val ≤ env.func_type_indices.val.length := by simpa using hnextbound
        simp only [Slice.length] at hlength hbound hcap ⊢
        omega
      obtain ⟨⟨reply, v'⟩, hsubmit, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases reply with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst out
        trivial
      | Ok u =>
        cases u
        have hsubmit' : visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') := hsubmit
        have hv' := hp.submit moduleId history issued v v' hv rfl hissued henv
          (by simpa [issued] using hinv.fresh) hsubmit'
        simp at h
        obtain ⟨nextId, hinc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        have hincspec := UScalar.add_equiv batchId 1#usize
        rw [hinc] at hincspec
        simp only [Result.ok.injEq] at h
        subst out
        refine ⟨history ++ [issued], ?_, hv', by simpa using hnext⟩
        exact hinv.issue issued nextPending finish next nextId rfl rfl rfl hissued rfl rfl hspan
          (by dsimp [issued]; have := hsubspec.1; have := hsubspec.2.1; omega)
          (by simpa using hnextbound) (by simpa using hincspec.2.1) hpushspec hroom

end Itasca.StreamSubmission

namespace Itasca.StreamSubmission
private theorem body_sound {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List StreamBatch.Issued)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : SoundInvariant code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : stream.submit_code_batches_loop.body source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config (alloc.vec.Vec.len env.func_type_indices) v pending pos func batchId = .ok out) :
    BodyPost Tracks code env start moduleId config.max_batches func out := by
  unfold stream.submit_code_batches_loop.body at h
  by_cases hmore : func < alloc.vec.Vec.len env.func_type_indices
  · rw [if_pos hmore] at h
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull] at h
      obtain ⟨⟨r, v', remaining⟩, hretire, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst out
        trivial
      | Ok u =>
        cases u
        have hentry : ∀ issued ∈ history, CodeEntry.Bounds issued.env := by
          intro issued hm
          have he := (hinv.issued issued hm).2.1
          simpa [he] using henv
        obtain ⟨hv', retiredId, hperm, hcomplete⟩ := StreamScheduler.retire_sound
          visitor Tracks hp moduleId history v v' pending remaining hv hentry hretire
        have hinv' := hinv.retire remaining retiredId hperm hcomplete
        have hlen : remaining.length + 1 = pending.length := by
          simpa [alloc.vec.Vec.length] using hperm.length_eq
        have hroom : remaining.length < config.max_batches.val := by
          have hb := hinv.pending_bound
          omega
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        exact resume_sound source visitor Tracks hp state moduleId env code start config v' remaining
          pos func batchId history environment tail hsource henv hcap hinv' hv'
          (by scalar_tac) hroom out h
    · rw [if_neg hfull] at h
      exact resume_sound source visitor Tracks hp state moduleId env code start config v pending
        pos func batchId history environment tail hsource henv hcap hinv hv
        (by scalar_tac) (by scalar_tac) out h
  · rw [if_neg hmore] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst out
      trivial
    · rename_i hpos
      simp only [Result.ok.injEq] at h
      subst out
      have hfunc : func = alloc.vec.Vec.len env.func_type_indices := by
        apply UScalar.eq_of_val_eq
        have hb := hinv.functions
        scalar_tac
      have hpos : pos = Slice.len code := by apply UScalar.eq_of_val_eq; simpa using hpos
      subst func
      subst pos
      exact ⟨history, batchId, hinv, hv⟩

end Itasca.StreamSubmission

namespace Itasca
/-- Following an accepted submission run, each successful iteration appends its seed to the
history and may retire one batch, which then has a completion certificate. -/
theorem stream.submit_code_batches_loop.sound {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List StreamBatch.Issued)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.SoundInvariant code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v)
    (finalPending : alloc.vec.Vec Usize) (finalV : V)
    (h : stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config v pending pos func batchId (alloc.vec.Vec.len env.func_type_indices) =
        .ok (.Ok finalPending, finalV)) :
    StreamSubmission.SoundPost Tracks code env start moduleId config.max_batches (.Ok finalPending, finalV) := by
  generalize hn : env.func_type_indices.val.length - func.val = n
  induction n using Nat.strong_induction_on generalizing v pending pos func batchId history with
  | h n ih =>
    unfold stream.submit_code_batches_loop at h
    rw [loop] at h
    obtain ⟨out, hbody, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hs := StreamSubmission.body_sound source visitor Tracks hp state moduleId env code start
      config v pending pos func batchId history environment tail hsource henv hcap hinv hv out hbody
    cases out with
    | done result =>
      have he : result = (.Ok finalPending, finalV) := by simpa using hrest
      subst result
      exact hs
    | cont next =>
      obtain ⟨v', pending', pos', func', batchId'⟩ := next
      obtain ⟨history', hinv', hv', hprogress⟩ := hs
      have hlt : env.func_type_indices.val.length - func'.val < n := by
        have hb := hinv'.functions
        omega
      have hrecursive : stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
          env.globals env.exports env.elements env.data_count env.declared_funcs env.start
          env.func_type_indices env.func_types
          env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
          (Slice.len code) config v' pending' pos' func' batchId' (alloc.vec.Vec.len env.func_type_indices) =
            .ok (.Ok finalPending, finalV) := hrest
      exact ih _ hlt v' pending' pos' func' batchId' history' hinv' hv' hrecursive rfl

/-- Accepted submission gives a complete ordered byte and function partition, the issued
identities, bounded distinct pending IDs, and certificates for retired work. Source coherence and
scheduler provenance are the only embedding premises. Callbacks that the run did not reach need
not return. -/
theorem stream.submit_code_batches.sound {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize) (v' : V)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val) (hstart : start.val ≤ code.length)
    (hv : Tracks moduleId [] v)
    (h : stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config v =
      .ok (.Ok pending, v')) :
    StreamSubmission.SoundPost Tracks code env start moduleId config.max_batches (.Ok pending, v') := by
  exact stream.submit_code_batches_loop.sound source visitor Tracks hp state moduleId env code start
    config v (alloc.vec.Vec.new _) start 0#usize 0#usize [] environment tail hsource henv hcap
    (StreamSubmission.SoundInvariant.initial code env start moduleId config.max_batches hstart) hv pending v' h

end Itasca

end
