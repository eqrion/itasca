import Itasca.Support.Translation
import Itasca.Stream.RetirementAndFraming
import Itasca.Module.Layout
import Itasca.Module.Code.FuncTyping
import Itasca.Module.Env.Complete

namespace Itasca.metadata.CodeMetadata
open Aeneas Aeneas.Std

/-- The number of defined functions as a machine index for the driver loop. -/
def definedCount (env : CodeMetadata) : Usize :=
  Usize.ofNatCore (Translation.Environment.definedTypeIndices env).length (by
    have bound := env.funcs.property
    simp only [Translation.Environment.definedTypeIndices, List.length_map, List.length_drop]
    scalar_tac)

@[simp, scalar_tac_simps] theorem definedCount_val (env : CodeMetadata) :
    env.definedCount.val = (Translation.Environment.definedTypeIndices env).length := by
  simp [definedCount]

theorem num_func_defs_eq (env : CodeMetadata) (h : env.num_imported_funcs.val ≤ env.funcs.val.length) :
    env.num_func_defs = .ok env.definedCount := by
  obtain ⟨n, call, hn⟩ := WP.spec_imp_exists (num_func_defs.spec env h)
  have same : n = env.definedCount := by
    apply UScalar.eq_of_val_eq
    simp [Translation.Environment.definedTypeIndices, hn]
  simpa [same] using call

end Itasca.metadata.CodeMetadata


/-!
Proofs for Stream.

This module collects SubmissionSound, BatchFramingComplete, Soundness, SplitComplete.
Each section documents its contracts and consumers.
-/

/-! ## SubmissionSound -/

section

/-!
# Submission Sound

Framing steps and source partitions establish sound submitted batches. The submission relation retains exact entry boundaries and validation evidence.
-/

/-! ## FramingStep -/

section

/-!
# Single framing step

Specification of one iteration, `stream.get_next_batch_loop.body`, of the batch framing loop.
`Stream.Framing.BatchStepPost` combines the arithmetic invariant with `Stream.Framing.FrameStep`,
which records the actual view read, the decoded entry size and the consecutive entry boundaries.
`stream.get_next_batch_loop.body.accepted` derives the step facts from an ordinary return of the
body, so no premise is placed on source calls that were not reached.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Framing

/-- A continuing framing step either does not take another entry, or
records the exact returned view, decoded length and consecutive boundaries. -/
def FrameStep {S : Type} (source : stream.StreamingSource S) (state : S) (codeLen q i : Usize) :
    ControlFlow (Usize × Usize × Usize × Bool)
      (core.result.Result (Usize × Usize) error.Error) → Prop
  | .done (.Ok (finish, next)) => finish = q ∧ next = i
  | .done (.Err _) => True
  | .cont (finish, next, _, _) =>
      (finish = q ∧ next = i) ∨
        ∃ (view : Slice U8) (viewEnd : Usize) (size : U32) (prefixLen content : Usize),
          stream.read_exact source state q viewEnd = .ok (.Ok view) ∧
          viewEnd.val = Nat.min codeLen.val (q.val + 5) ∧
          Binary.Leb128.Decoded view 0#usize size prefixLen ∧
          content.val = q.val + prefixLen.val ∧
          finish.val = content.val + size.val ∧
          finish.val ≤ codeLen.val ∧ next.val = i.val + 1

/-- Arithmetic preservation and the observed extent of one extracted step. -/
def BatchStepPost {S : Type} (source : stream.StreamingSource S) (state : S)
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

end Itasca.Stream.Framing

namespace Itasca

/-- The extracted loop body preserves the arithmetic invariant and records each consumed declared
extent, under a return premise only for the code read it reaches. -/
theorem stream.get_next_batch_loop.body.spec {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen start first num threshold q i b : Usize) (stopped : Bool)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : Stream.Framing.BatchInvariant codeLen start first num threshold q i b stopped)
    (hprogress : first.val < i.val → start.val < q.val)
    (hreturn : i.val < num.val → stopped = false → ∀ last,
      last.val = Nat.min codeLen.val (q.val + 5) → ∃ r, source.code state q last = .ok r) :
    stream.get_next_batch_loop.body source state codeLen first num threshold q i b stopped ⦃ r =>
      (match r with
       | .done result => Stream.Framing.BatchPost codeLen start first num result
       | .cont (q', i', b', stopped') =>
           (Stream.Framing.BatchInvariant codeLen start first num threshold q' i' b' stopped' ∧
             (first.val < i'.val → start.val < q'.val)) ∧
             (2 * (num.val - i'.val) + if stopped' then 0 else 1) <
               (2 * (num.val - i.val) + if stopped then 0 else 1)) ∧
      Stream.Framing.FrameStep source state codeLen q i r ⦄ := by
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
      simpa [Stream.Framing.BatchPost, Stream.Framing.FrameStep] using
        ⟨hprogress hlt, hq, hlt, hi⟩
    · rename_i hnotstop
      have hfalse : stopped = false := by cases stopped <;> simp_all
      have hiroom : i.val + 1 ≤ Usize.max := by scalar_tac
      have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
        have := Module.Code.module_room
        simp only [limits.MAX_LEB_BYTES]
        scalar_tac
      obtain ⟨need, hneed, hneedval⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := q) (y := limits.MAX_LEB_BYTES) (by scalar_tac))
      rw [hneed]
      simp only [bind_ok, lift]
      have hviewend : (core.cmp.impls.OrdUsize.min codeLen need).val =
          Nat.min codeLen.val (q.val + 5) := by
        rw [Stream.Framing.min_val, hneedval]
        simp [limits.MAX_LEB_BYTES]
      have horder : q.val ≤ (core.cmp.impls.OrdUsize.min codeLen need).val := by
        rw [hviewend]
        exact Nat.le_min.mpr ⟨hq, by omega⟩
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_exact.spec source state q
        (core.cmp.impls.OrdUsize.min codeLen need) horder (hreturn (by exact himore) hfalse _ hviewend))
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost, Stream.Framing.FrameStep]
      | Ok view =>
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨r, hl, hlp⟩ := WP.spec_imp_exists (stream.read_len.spec view 0#usize)
        rw [hl]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost, Stream.Framing.FrameStep]
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
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost, Stream.Framing.FrameStep]
            | Ok content =>
              simp
              obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
              rw [hf]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost, Stream.Framing.FrameStep]
              | Ok finish =>
                simp
                split
                · simp [Stream.Framing.BatchPost, Stream.Framing.FrameStep]
                · rename_i hfinish
                  have hfbound : finish.val ≤ codeLen.val := by scalar_tac
                  have hbroom : b.val + len.val ≤ Usize.max := by
                    simp only [hbzero]
                    scalar_tac
                  step
                  step
                  have ha := Stream.Framing.advance (num := num) (threshold := threshold)
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
            · simp only [WP.spec_ok, Stream.Framing.BatchInvariant]
              constructor
              · refine ⟨⟨hstart, hq, hfirst, hi, hb, ?_, ?_⟩, hprogress, ?_⟩
                · intro he; exact False.elim (hne he)
                · intro he; cases he
                · simp
              · exact .inl ⟨rfl, rfl⟩
            · obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec q prefixLen)
              rw [hc]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost, Stream.Framing.FrameStep]
              | Ok content =>
                simp
                obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
                rw [hf]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost, Stream.Framing.FrameStep]
                | Ok finish =>
                  simp
                  split
                  · simp [Stream.Framing.BatchPost, Stream.Framing.FrameStep]
                  · rename_i hfinish
                    have hfbound : finish.val ≤ codeLen.val := by scalar_tac
                    have hbroom : b.val + len.val ≤ Usize.max := by
                      have hfmax := hfp.2
                      have := Module.Code.module_room
                      scalar_tac
                    step
                    step
                    have ha := Stream.Framing.advance (num := num) (threshold := threshold)
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
    simpa [Stream.Framing.BatchPost, Stream.Framing.FrameStep] using
      ⟨hprogress (by omega), hq, (by omega : first.val < i.val), hi⟩

/-- An ordinary return of the loop body reveals the reached source callback;
no return assumption is imposed on any unexecuted source operation. -/
theorem stream.get_next_batch_loop.body.accepted {S : Type}
    (source : stream.StreamingSource S) (state : S)
    (codeLen start first num threshold q i b : Usize) (stopped : Bool)
    (reply : ControlFlow (Usize × Usize × Usize × Bool)
      (core.result.Result (Usize × Usize) error.Error))
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : Stream.Framing.BatchInvariant codeLen start first num threshold q i b stopped)
    (hprogress : first.val < i.val → start.val < q.val)
    (h : stream.get_next_batch_loop.body source state codeLen first num threshold q i b stopped =
      .ok reply) :
    Stream.Framing.BatchStepPost source state codeLen start first num threshold q i stopped reply := by
  have hreturn : i.val < num.val → stopped = false → ∀ last : Usize,
      last.val = Nat.min codeLen.val (q.val + 5) → ∃ r, source.code state q last = .ok r := by
    intro hi hstop last hlast
    have hr := h
    have hiless : i < num := by exact hi
    simp only [stream.get_next_batch_loop.body, hiless, hstop, Bool.false_eq_true,
      ↓reduceIte] at hr
    obtain ⟨need, hneed, hr⟩ := Computation.bind_ok_inv _ _ _ hr
    have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
      have hq := hinv.2.1
      have := Module.Code.module_room
      simp only [limits.MAX_LEB_BYTES]
      scalar_tac
    have hneedval := UScalar.add_spec (x := q) (y := limits.MAX_LEB_BYTES) (by scalar_tac)
    simp only [hneed, WP.spec_ok] at hneedval
    have hend : core.cmp.impls.OrdUsize.min codeLen need = last := by
      apply UScalar.eq_of_val_eq
      rw [Stream.Framing.min_val, hneedval, hlast]
      simp [limits.MAX_LEB_BYTES]
    simp only [lift, bind_ok, hend] at hr
    obtain ⟨r, hread, _⟩ := Computation.bind_ok_inv _ _ _ hr
    unfold stream.read_exact at hread
    obtain ⟨r, hsource, _⟩ := Computation.bind_ok_inv _ _ _ hread
    exact ⟨r, hsource⟩
  have hs := stream.get_next_batch_loop.body.spec source state codeLen start first num threshold
    q i b stopped hcap hmore hinv hprogress hreturn
  simpa only [h, WP.spec_ok, Stream.Framing.BatchStepPost] using hs

end Itasca

end

/-! ## FramingSound -/

section

/-!
# Batch framing soundness

`FrameStep.extent` transports each reached length-prefix read through source
coherence into an independent code-entry extent. The accepted-loop induction
folds those actual reads; `stream.get_next_batch.sound` gives strict byte and
function progress and the driver bounds. It needs no premise on source calls
that the run did not reach.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Framing

/-- Coherence transports each actually read length prefix into the fixed code
region, yielding an independent extent without requiring source availability. -/
theorem FrameStep.extent {S : Type} (source : stream.StreamingSource S) (state : S)
    (environment tail : List U8) (code : Slice U8)
    (hc : Stream.Source.Coherent source state environment code.val tail)
    (codeLen q i finish next bytes : Usize) (stopped : Bool)
    (hlen : codeLen.val = code.length) (hq : q.val ≤ codeLen.val)
    (h : FrameStep source state codeLen q i (.cont (finish, next, bytes, stopped))) :
    (finish = q ∧ next = i) ∨
      ∃ content, Module.Code.Extent code q content finish ∧ next.val = i.val + 1 := by
  rcases h with he | ⟨view, viewEnd, size, prefixLen, content,
    hread, hviewend, hdecoded, hcontent, hfinish, hbound, hnext⟩
  · exact .inl he
  · have horder : q.val ≤ viewEnd.val := by rw [hviewend]; exact Nat.le_min.mpr ⟨hq, by omega⟩
    have hend : viewEnd.val ≤ code.length := by
      rw [hviewend, ← hlen]
      exact Nat.min_le_left _ _
    obtain ⟨hview, _⟩ := stream.read_exact.sound source state environment code.val tail hc q viewEnd
      view horder hend hread
    have hprefix : Binary.Leb128.Decoded code q size content :=
      hdecoded.of_slice_view horder hend hview (by simp) hcontent
    exact .inr ⟨content, ⟨size, hprefix, hfinish, by omega⟩, hnext⟩

end Itasca.Stream.Framing

namespace Itasca

/-- Fold an invariant over the prefix reads actually reached by an accepted
batch loop. Source callback totality is deliberately unnecessary. -/
theorem stream.get_next_batch_loop.accepted_induction {S : Type}
    (source : stream.StreamingSource S) (state : S)
    (codeLen start first num threshold : Usize)
    (P : Usize → Usize → Prop)
    (hstep : ∀ q i finish next bytes stopped, P q i →
      Stream.Framing.FrameStep source state codeLen q i (.cont (finish, next, bytes, stopped)) →
      P finish next)
    (q i b : Usize) (stopped : Bool) (finish next : Usize)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : Stream.Framing.BatchInvariant codeLen start first num threshold q i b stopped)
    (hprogress : first.val < i.val → start.val < q.val)
    (hp : P q i)
    (h : stream.get_next_batch_loop source state codeLen first num threshold q i b stopped =
      .ok (.Ok (finish, next))) :
    Stream.Framing.BatchPost codeLen start first num (.Ok (finish, next)) ∧ P finish next := by
  generalize hm : (2 * (num.val - i.val) + if stopped then 0 else 1) = n
  induction n using Nat.strong_induction_on generalizing q i b stopped with
  | h n ih =>
    unfold stream.get_next_batch_loop at h
    rw [loop] at h
    obtain ⟨reply, hbody, hrest⟩ := Computation.bind_ok_inv _ _ _ h
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
theorem stream.get_next_batch.sound {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen start first num threshold finish next : Usize)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hstart : start.val ≤ codeLen.val) (hmore : first.val < num.val)
    (h : stream.get_next_batch source state codeLen start first num threshold =
      .ok (.Ok (finish, next))) :
    start.val < finish.val ∧ finish.val ≤ codeLen.val ∧
      first.val < next.val ∧ next.val ≤ num.val := by
  apply (stream.get_next_batch_loop.accepted_induction source state codeLen start first num threshold
    (fun _ _ => True) (by intros; trivial) start first 0#usize false finish next hcap hmore
    (by simp [Stream.Framing.BatchInvariant, hstart]; omega) (by omega) trivial h).1

end Itasca

end

/-! ## Partition -/

section

/-!
# Batch partitions

`Stream.Scheduler.Partition` records that a list of issued batches covers consecutive intervals of
the code region and consecutive defined-function indices, in submission order.
`Stream.Scheduler.Partition.encoding` and `Stream.Scheduler.Partition.code` assemble the per-batch
`Stream.Scheduler.Completed` certificates into one encoded and typed code section for the whole
module.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Scheduler
/-- Issued batches partition bytes and defined-function indices in submission
order. Worker completion order is deliberately absent from this relation. -/
inductive Partition (code : Slice U8) (env : metadata.CodeMetadata) :
    Usize → Nat → List Stream.Batch.Issued → Usize → Nat → Prop where
  | nil (pos : Usize) (func : Nat) : pos.val ≤ code.length →
      Partition code env pos func [] pos func
  | cons {pos func issued rest middle finish next} :
      issued.env = env → issued.code_offset = pos → issued.first_func.val = func →
      Body.Scalar.BytesAt code pos issued.code.val middle →
      Partition code env middle (func + issued.num_funcs.val) rest finish next →
      Partition code env pos func (issued :: rest) finish next

/-- Appending the next issued batch extends a partition. -/
theorem Partition.snoc {code env pos func history middle next issued finish}
    (h : Partition code env pos func history middle next)
    (henv : issued.env = env) (hoffset : issued.code_offset = middle)
    (hfunc : issued.first_func.val = next)
    (hbytes : Body.Scalar.BytesAt code middle issued.code.val finish) :
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
      Binary.At (Binary.Rep (CodeEntry.CodeEncoding)) code pos entries finish ∧
      Module.Code.EntriesTyped env func entries := by
  induction h with
  | nil pos func hbound =>
    exact ⟨[], by simp, ⟨[], .nil, Body.Scalar.BytesAt.nil _ _ hbound⟩, .nil _⟩
  | @cons pos func issued rest middle finish next he ho hf hb hp ih =>
    obtain ⟨entries, hn, hr, ht⟩ := hcompleted issued (by simp)
    obtain ⟨restEntries, hnext, hrestBytes, hrestTyped⟩ := ih (fun issued hm => hcompleted issued (by simp [hm]))
    have hfirst : Module.Code.EntriesTyped env func entries := by simpa [he, hf] using ht
    refine ⟨entries ++ restEntries, ?_, Module.Code.entries_at_append ⟨issued.code.val, hr, hb⟩ hrestBytes,
      hfirst.append (by simpa [hn] using hrestTyped)⟩
    simp only [List.length_append]
    omega

/-- A checked header and a partition of the whole code region give the padded code section
encoding and the pairing of each declared function type with its typed code entry. -/
theorem Partition.code {code env entries history}
    (hheader : Stream.Framing.HeaderAt code env entries)
    (h : Partition code env entries 0 history (Slice.len code) (Translation.Environment.definedTypeIndices env).length)
    (hcompleted : ∀ issued ∈ history, Completed issued) :
    ∃ codes, Binary.PaddedEncoding 10#u8
      (Binary.VecEncoding (CodeEntry.CodeEncoding)) [] codes code.val ∧
      List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) (Translation.Environment.definedTypeIndices env) codes := by
  obtain ⟨codes, hn, hb, ht⟩ := h.encoding hcompleted
  have hcount : codes.length = (Translation.Environment.definedTypeIndices env).length := by omega
  have htyped := ht.forall₂ (by omega)
  rcases hheader with ⟨hbytes, _, hfuncs⟩ | ⟨count, hs, _⟩
  · have hcodes : codes = [] := by simpa [hfuncs] using hcount
    refine ⟨codes, ?_, by simpa using htyped⟩
    simp only [hcodes, hbytes]
    exact ⟨[], [], .nil, .absent, rfl⟩
  · obtain ⟨bytes, he, hspan⟩ := Module.Code.Section.encoding hs hb hcount
    have heq : code.val = bytes := by simpa using hspan.suffix
    exact ⟨codes, ⟨[], code.val, .nil, heq ▸ he, rfl⟩, by simpa using htyped⟩

end Itasca.Stream.Scheduler

end

/-! ## SubmissionSound -/

section

/-!
# Submission soundness

Soundness of `stream.submit_code_batches` over a coherent source and a scheduler with
`Stream.Scheduler.Provenance`. `Stream.Submission.SoundInvariant` holds along the submission loop:
the issued batches partition the code region in order, batch IDs are numbered consecutively, the
pending IDs are distinct and bounded, and every issued batch is pending or completed.
`stream.submit_code_batches.sound` gives `Stream.Submission.SoundPost` for an accepted run.
Completed certificates arise only from successful retirements in the loop, never from a premise
on the scheduler. Unreached callbacks need not return.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Submission
open Stream.Scheduler

/-- Invariant of a successful submission prefix: issued batches tile the code region in issuance
order, batch IDs are numbered consecutively, the pending IDs are distinct and bounded by the
capacity, and every issued batch is pending or has a completion certificate from a successful
retirement. -/
structure SoundInvariant (code : Slice U8) (env : metadata.CodeMetadata) (start : Usize)
    (id : U64) (capacity : Usize) (history : List Stream.Batch.Issued)
    (pending : alloc.vec.Vec Usize) (pos func nextId : Usize) : Prop where
  partition : Partition code env start 0 history pos func.val
  position : pos.val ≤ code.length
  functions : func.val ≤ (Translation.Environment.definedTypeIndices env).length
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
theorem SoundInvariant.initial (code : Slice U8) (env : metadata.CodeMetadata) (start : Usize)
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
    (issued : Stream.Batch.Issued) (nextPending : alloc.vec.Vec Usize)
    (finish nextFunc nextBatchId : Usize)
    (hmodule : issued.module_id = id) (henv : issued.env = env)
    (hbatch : issued.batch_id = nextId) (hbounded : issued.Bounded)
    (hoffset : issued.code_offset = pos) (hfirst : issued.first_func = func)
    (hbytes : Body.Scalar.BytesAt code pos issued.code.val finish)
    (hcount : nextFunc.val = func.val + issued.num_funcs.val)
    (hfunctions : nextFunc.val ≤ (Translation.Environment.definedTypeIndices env).length)
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
def SoundPost {V : Type} (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.CodeMetadata) (start : Usize) (id : U64) (capacity : Usize) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ history nextId,
      SoundInvariant code env start id capacity history pending (Slice.len code)
        (env.definedCount) nextId ∧ Tracks id history v
  | (.Err _, _) => True

private def BodyPost {V : Type} (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.CodeMetadata) (start : Usize) (id : U64)
    (capacity func : Usize) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => SoundPost Tracks code env start id capacity result
  | .cont (v, pending, pos, next, batchId) => ∃ history,
      SoundInvariant code env start id capacity history pending pos next batchId ∧
      Tracks id history v ∧ func.val < next.val

end Itasca.Stream.Submission

namespace Itasca.Stream.Submission
private theorem resume_sound {S V : Type} (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Stream.Scheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8) (start : Usize)
    (config : stream.StreamingConfig) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List Stream.Batch.Issued)
    (environment tail : List U8) (hsource : Stream.Source.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : SoundInvariant code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v) (hfunc : func.val < (Translation.Environment.definedTypeIndices env).length)
    (hroom : pending.length < config.max_batches.val)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : (do
      let r ← stream.get_next_batch source state (Slice.len code) pos func (env.definedCount) config.batch_bytes
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (finish, next) := val
        let r1 ← stream.read_exact source state pos finish
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue bytes =>
          let pending1 ← alloc.vec.Vec.push pending batchId
          let shared ← stream.share_code env
          let count ← next - func
          let (r2, v') ← visitor.submit_code_batch v
            { module_id := moduleId, batch_id := batchId, env := shared, code := bytes,
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
  obtain ⟨r, hframe, h⟩ := Computation.bind_ok_inv _ _ _ h
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    subst out
    trivial
  | Ok pair =>
    obtain ⟨finish, next⟩ := pair
    obtain ⟨hprogress, hfinish, hnext, hnextbound⟩ := stream.get_next_batch.sound source state
      (Slice.len code) pos func (env.definedCount) config.batch_bytes finish next
      (by simpa using hcap) (by simpa using hinv.position) (by simpa using hfunc) hframe
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hread, h⟩ := Computation.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      subst out
      trivial
    | Ok bytes =>
      have hview := stream.read_exact.sound source state environment code.val tail hsource
        pos finish bytes (by omega) (by simpa using hfinish) hread
      have hspan := Body.Scalar.BytesAt.of_slice_view (by omega : pos.val ≤ finish.val)
        (by simpa using hfinish : finish.val ≤ code.length) hview.1
      simp at h
      obtain ⟨nextPending, hpush, h⟩ := Computation.bind_ok_inv _ _ _ h
      have hpushspec := alloc.vec.Vec.push_spec pending batchId (by scalar_tac)
      rw [hpush] at hpushspec
      simp only [WP.spec_ok] at hpushspec
      obtain ⟨shared, hshared, h⟩ := Computation.bind_ok_inv _ _ _ h
      have eq : env = shared := by simpa [stream.share_code] using hshared
      subst shared
      obtain ⟨count, hsub, h⟩ := Computation.bind_ok_inv _ _ _ h
      have hsubspec := UScalar.sub_equiv next func
      rw [hsub] at hsubspec
      let issued : Stream.Batch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count⟩
      have hissued : issued.Bounded := by
        dsimp [issued, Stream.Batch.Issued.Bounded]
        have hlength := hspan.length
        change finish.val = pos.val + bytes.length at hlength
        have hbound := hspan.bound
        have hcountval := hsubspec.2.1
        have hnextbound' : next.val ≤ (Translation.Environment.definedTypeIndices env).length := by simpa using hnextbound
        simp only [Slice.length] at hlength hbound hcap ⊢
        omega
      obtain ⟨⟨reply, v'⟩, hsubmit, h⟩ := Computation.bind_ok_inv _ _ _ h
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
        obtain ⟨nextId, hinc, h⟩ := Computation.bind_ok_inv _ _ _ h
        have hincspec := UScalar.add_equiv batchId 1#usize
        rw [hinc] at hincspec
        simp only [Result.ok.injEq] at h
        subst out
        refine ⟨history ++ [issued], ?_, hv', by simpa using hnext⟩
        exact hinv.issue issued nextPending finish next nextId rfl rfl rfl hissued rfl rfl hspan
          (by dsimp [issued]; have := hsubspec.1; have := hsubspec.2.1; omega)
          (by simpa using hnextbound) (by simpa using hincspec.2.1) hpushspec hroom

end Itasca.Stream.Submission

namespace Itasca.Stream.Submission
private theorem body_sound {S V : Type} (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Stream.Scheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8) (start : Usize)
    (config : stream.StreamingConfig) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List Stream.Batch.Issued)
    (environment tail : List U8) (hsource : Stream.Source.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : SoundInvariant code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : stream.submit_code_batches_loop.body source visitor moduleId state env
      (Slice.len code) config (env.definedCount) v pending pos func batchId = .ok out) :
    BodyPost Tracks code env start moduleId config.max_batches func out := by
  unfold stream.submit_code_batches_loop.body at h
  by_cases hmore : func < env.definedCount
  · rw [if_pos hmore] at h
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull] at h
      obtain ⟨⟨r, v', remaining⟩, hretire, h⟩ := Computation.bind_ok_inv _ _ _ h
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
        obtain ⟨hv', retiredId, hperm, hcomplete⟩ := Stream.Scheduler.retire_sound
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
      have hfunc : func = env.definedCount := by
        apply UScalar.eq_of_val_eq
        have hb := hinv.functions
        scalar_tac
      have hpos : pos = Slice.len code := by apply UScalar.eq_of_val_eq; simpa using hpos
      subst func
      subst pos
      exact ⟨history, batchId, hinv, hv⟩

end Itasca.Stream.Submission

namespace Itasca
/-- Following an accepted submission run, each successful iteration appends its seed to the
history and may retire one batch, which then has a completion certificate. -/
theorem stream.submit_code_batches_loop.sound {S V : Type}
    (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Stream.Scheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8) (start : Usize)
    (config : stream.StreamingConfig) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List Stream.Batch.Issued)
    (environment tail : List U8) (hsource : Stream.Source.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : Stream.Submission.SoundInvariant code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v)
    (finalPending : alloc.vec.Vec Usize) (finalV : V)
    (h : stream.submit_code_batches_loop source visitor moduleId state env
      (Slice.len code) config v pending pos func batchId (env.definedCount) =
        .ok (.Ok finalPending, finalV)) :
    Stream.Submission.SoundPost Tracks code env start moduleId config.max_batches (.Ok finalPending, finalV) := by
  generalize hn : (Translation.Environment.definedTypeIndices env).length - func.val = n
  induction n using Nat.strong_induction_on generalizing v pending pos func batchId history with
  | h n ih =>
    unfold stream.submit_code_batches_loop at h
    rw [loop] at h
    obtain ⟨out, hbody, hrest⟩ := Computation.bind_ok_inv _ _ _ h
    have hs := Stream.Submission.body_sound source visitor Tracks hp state moduleId env code start
      config v pending pos func batchId history environment tail hsource henv hcap hinv hv out hbody
    cases out with
    | done result =>
      have he : result = (.Ok finalPending, finalV) := by simpa using hrest
      subst result
      exact hs
    | cont next =>
      obtain ⟨v', pending', pos', func', batchId'⟩ := next
      obtain ⟨history', hinv', hv', hprogress⟩ := hs
      have hlt : (Translation.Environment.definedTypeIndices env).length - func'.val < n := by
        have hb := hinv'.functions
        omega
      have hrecursive : stream.submit_code_batches_loop source visitor moduleId state env
          (Slice.len code) config v' pending' pos' func' batchId' (env.definedCount) =
            .ok (.Ok finalPending, finalV) := hrest
      exact ih _ hlt v' pending' pos' func' batchId' history' hinv' hv' hrecursive rfl

/-- Accepted submission gives a complete ordered byte and function partition, the issued
identities, bounded distinct pending IDs, and certificates for retired work. Source coherence and
scheduler provenance are the only embedding premises. Callbacks that the run did not reach need
not return. -/
theorem stream.submit_code_batches.sound {S V : Type}
    (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Stream.Scheduler.Provenance visitor Tracks )
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (code : Slice U8) (start : Usize)
    (config : stream.StreamingConfig) (v : V) (pending : alloc.vec.Vec Usize) (v' : V)
    (environment tail : List U8) (hsource : Stream.Source.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val) (hstart : start.val ≤ code.length)
    (hv : Tracks moduleId [] v)
    (h : stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config v =
      .ok (.Ok pending, v')) :
    Stream.Submission.SoundPost Tracks code env start moduleId config.max_batches (.Ok pending, v') := by
  simp only [stream.submit_code_batches, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
    env.num_func_defs_eq henv.1, bind_ok] at h
  exact stream.submit_code_batches_loop.sound source visitor Tracks hp state moduleId env code start
    config v (alloc.vec.Vec.new _) start 0#usize 0#usize [] environment tail hsource henv hcap
    (Stream.Submission.SoundInvariant.initial code env start moduleId config.max_batches hstart) hv pending v' h

end Itasca

end

end

/-! ## BatchFramingComplete -/

section

/-!
# Batch framing completeness

Available code bytes and independent entry spans construct successful next-batch reads.
Source-view and byte-repetition transport retain the exact framed slice.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Source

/-- Available immutable views determine every successful source observation. -/
theorem Available.coherent {S : Type} {source : stream.StreamingSource S} {state : S}
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

end Itasca.Stream.Source

namespace Itasca
private theorem batch_prefix_read {S : Type} (source : stream.StreamingSource S) (state : S)
    (environment tail : List U8) (code : Slice U8)
    (ha : Stream.Source.Available source state environment code.val tail)
    (codeLen q content finish : Usize) (hlen : codeLen.val = code.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hext : Module.Code.Extent code q content finish) :
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
    have := Module.Code.module_room
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
  have hdview : Binary.Leb128.Decoded view 0#usize size prefixLen :=
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
    (source : stream.StreamingSource S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : Stream.Source.Available source state environment code.val tail)
    (codeLen start first num threshold q i b : Usize) (stopped : Bool)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : Stream.Framing.BatchInvariant codeLen start first num threshold q i b stopped)
    (hentry : i.val < num.val → stopped = false →
      ∃ content finish, Module.Code.Extent code q content finish) :
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

open Binary

/-- Successful batching splits the independently encoded entry list into a nonempty prefix and
the remaining suffix. The prefix and suffix satisfy the same entry relation `R` as the input, so
a relation that carries body and local limits is preserved through framing. -/
theorem stream.get_next_batch.complete_spec {S : Type}
    (source : stream.StreamingSource S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : Stream.Source.Available source state environment code.val tail)
    (R : Code → List U8 → Prop) (hencoding : ∀ entry bytes, R entry bytes → CodeEntry.CodeEncoding entry bytes)
    (codeLen start first num threshold : Usize) (entries : List Code)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val) (hcount : first.val + entries.length = num.val)
    (hbytes : At (Rep R) code start entries codeLen) :
    stream.get_next_batch source state codeLen start first num threshold ⦃ r =>
      ∃ finish next taken rest, r = .Ok (finish, next) ∧
        Stream.Framing.BatchPost codeLen start first num (.Ok (finish, next)) ∧
        entries = taken ++ rest ∧ taken ≠ [] ∧
        next.val = first.val + taken.length ∧ num.val = next.val + rest.length ∧
        At (Rep R) code start taken finish ∧ At (Rep R) code finish rest codeLen ⦄ := by
  have hextent {q finish : Usize} {entry : Code} (h : At R code q entry finish) :
      ∃ content, Module.Code.Extent code q content finish := by
    obtain ⟨bytes, he, hs⟩ := h
    exact (show At CodeEntry.CodeEncoding code q entry finish from ⟨bytes, hencoding entry bytes he, hs⟩).code_extent
  unfold stream.get_next_batch stream.get_next_batch_loop
  apply loop.spec_decr_nat
    (fun s => 2 * (num.val - s.2.1.val) + if s.2.2.2 then 0 else 1)
    (fun s =>
      Stream.Framing.BatchInvariant codeLen start first num threshold s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
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
        ∃ content finish, Module.Code.Extent code q content finish := by
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
      rcases Stream.Framing.FrameStep.extent source state environment tail code ha.coherent
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
          obtain ⟨hsize, hcontent⟩ := Module.Code.decoded_unique hd hd'
          have hmiddle : middle = q' := by apply UScalar.eq_of_val_eq; rw [hend, hend', ← hcontent, ← hsize]
          subst middle
          refine ⟨taken ++ [entry], rest, ?_, ?_, ?_, htaken.rep_snoc he, hr⟩
          · simpa [List.append_assoc] using heq
          · simp only [List.length_append, List.length_singleton]; omega
          · simp only [List.length_cons] at hnrest; omega
  · have hstart : start.val ≤ codeLen.val := hbytes.span.1
    dsimp only
    refine ⟨?_, by omega, [], entries, by simp, by simp, hcount.symm, ?_, hbytes⟩
    · simp [Stream.Framing.BatchInvariant, hstart]
      omega
    · exact ⟨[], .nil, Body.Scalar.BytesAt.nil code start (by omega)⟩

/-- Independently encoded entries within the implementation limits are batched successfully, returning
the nonempty encoded prefix and the unconsumed suffix. -/
theorem stream.get_next_batch.complete {S : Type}
    (source : stream.StreamingSource S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : Stream.Source.Available source state environment code.val tail)
    (codeLen start first num threshold : Usize) (entries : List Code)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val) (hcount : first.val + entries.length = num.val)
    (hbytes : At (Rep CodeEntry.CodeEncodingWithinLimits) code start entries codeLen) :
    ∃ finish next taken rest,
      stream.get_next_batch source state codeLen start first num threshold = .ok (.Ok (finish, next)) ∧
      Stream.Framing.BatchPost codeLen start first num (.Ok (finish, next)) ∧
      entries = taken ++ rest ∧ taken ≠ [] ∧
      next.val = first.val + taken.length ∧ num.val = next.val + rest.length ∧
      At (Rep CodeEntry.CodeEncodingWithinLimits) code start taken finish ∧
      At (Rep CodeEntry.CodeEncodingWithinLimits) code finish rest codeLen := by
  obtain ⟨r, hr, finish, next, taken, rest, rfl, hp⟩ := WP.spec_imp_exists
    (stream.get_next_batch.complete_spec source state environment tail code ha CodeEntry.CodeEncodingWithinLimits
      (fun _ _ h => h.encoding) codeLen start first num threshold entries hlen hcap hmore hcount hbytes)
  exact ⟨finish, next, taken, rest, hr, hp⟩

/-- An available exact source view carries precisely the independently
encoded entries in the corresponding interval of the logical code region. -/
theorem stream.read_exact.complete_rep {S A : Type}
    (source : stream.StreamingSource S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : Stream.Source.Available source state environment code.val tail)
    (R : A → List U8 → Prop) (start finish : Usize) (entries : List A)
    (hbytes : At (Rep R) code start entries finish) :
    ∃ view, stream.read_exact source state start finish = .ok (.Ok view) ∧
      Body.Scalar.BytesAt code start view.val finish ∧ Rep R entries view.val := by
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
  have hvspan := Body.Scalar.BytesAt.of_slice_view ho hspan.bound hview
  have heq : bytes = view.val := List.append_cancel_right (hspan.suffix.symm.trans hvspan.suffix)
  exact ⟨view, stream.read_exact.complete source state start finish view ho hread hvlen,
    hvspan, heq ▸ hrep⟩

/-- Batching and the following exact read produce the worker's byte view, which encodes the taken
entries within the implementation limits. The entry counts of the batch and the suffix are tracked. -/
theorem stream.get_next_batch.complete_view {S : Type}
    (source : stream.StreamingSource S) (state : S) (environment tail : List U8) (code : Slice U8)
    (ha : Stream.Source.Available source state environment code.val tail)
    (codeLen start first num threshold : Usize) (entries : List Code)
    (hlen : codeLen.val = code.length) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val) (hcount : first.val + entries.length = num.val)
    (hbytes : At (Rep CodeEntry.CodeEncodingWithinLimits) code start entries codeLen) :
    ∃ finish next taken rest view,
      stream.get_next_batch source state codeLen start first num threshold = .ok (.Ok (finish, next)) ∧
      Stream.Framing.BatchPost codeLen start first num (.Ok (finish, next)) ∧
      entries = taken ++ rest ∧ taken ≠ [] ∧
      next.val = first.val + taken.length ∧ num.val = next.val + rest.length ∧
      At (Rep CodeEntry.CodeEncodingWithinLimits) code start taken finish ∧
      At (Rep CodeEntry.CodeEncodingWithinLimits) code finish rest codeLen ∧
      stream.read_exact source state start finish = .ok (.Ok view) ∧
      Body.Scalar.BytesAt code start view.val finish ∧ Rep CodeEntry.CodeEncodingWithinLimits taken view.val := by
  obtain ⟨finish, next, taken, rest, hrun, hp, heq, hne, hn, hr, htaken, hrest⟩ :=
    stream.get_next_batch.complete source state environment tail code ha codeLen start first num threshold
      entries hlen hcap hmore hcount hbytes
  obtain ⟨view, hread, hview, hrep⟩ := stream.read_exact.complete_rep source state environment tail code ha
    CodeEntry.CodeEncodingWithinLimits start finish taken htaken
  exact ⟨finish, next, taken, rest, view, hrun, hp, heq, hne, hn, hr, htaken, hrest, hread, hview, hrep⟩

end Itasca

end

/-! ## Soundness -/

section

/-!
# Streaming acceptance and retirement invariants

Driver acceptance combines coherent source regions, actual worker provenance and module
assembly into the public validation certificate. State-relative retirement contracts
support the same tracked scheduler invariant.
-/

/-! ## DriverSound -/

section

/-!
# Streaming driver soundness

`stream.validate_streaming.sound_core`: if `stream.validate_streaming` accepts, then the
concatenation of the source's environment, code and tail regions satisfies `Module.Sound.Validated`
for the returned environment and tail, and is within the module size cap. The premises are source
coherence (`Stream.Source.Coherent`) and scheduler provenance (`Stream.Scheduler.Provenance`), both
obligations on the embedding. Read errors and callback failures are allowed, and neither callback
termination nor a canonical region split is needed. `Itasca/Results/Stream` states the public
`sound`.
-/

open Aeneas Aeneas.Std

namespace Itasca
/-- Acceptance of the streaming driver certifies the concatenated bytes, its returned
environment, and the tail it actually received. Soundness requires coherent source views and
worker provenance, and does not require callback termination or prevalidated bodies. -/
theorem stream.validate_streaming.sound_core {S V : Type}
    (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop)
    (hp : Stream.Scheduler.Provenance visitor Tracks )
    (id : U64) (state : S) (v v' : V) (env : metadata.ModuleMetadata metadata.CodeMetadata)
    (data environment code tail : Slice U8)
    (hsource : Stream.Source.Coherent source state environment.val code.val tail.val)
    (hbytes : data.val = environment.val ++ code.val ++ tail.val)
    (hv : Tracks id [] v)
    (h : stream.validate_streaming source visitor id state v = .ok (.Ok env, v')) :
    Nonempty (Stream.Run.Accepted source visitor id state v v' env) ∧
      Module.Sound.Validated data env ∧
      data.length ≤ limits.MAX_MODULE_BYTES.val := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted source visitor id state v v' env h
  have heq := hsource.environment_eq run.environment run.environment_call
  have hteq := hsource.tail_eq run.remaining.tailBytes run.remaining.tail_call
  have hlen := hsource.code_len_eq run.remaining.codeLength run.remaining.length_call
  have he := limits.add_offset.spec 0#usize (Slice.len run.environment)
  rw [run.environment_bound] at he
  simp only [WP.spec_ok] at he
  have hc := limits.add_offset.spec run.environmentLength run.remaining.codeLength
  rw [run.remaining.code_bound] at hc
  simp only [WP.spec_ok] at hc
  have hm := limits.add_offset.spec run.remaining.codeEnd (Slice.len run.remaining.tailBytes)
  rw [run.remaining.module_bound] at hm
  simp only [WP.spec_ok] at hm
  have hend : run.environmentLength = Slice.len run.environment := by
    apply UScalar.eq_of_val_eq
    simpa using he.1
  have hcap : code.length ≤ limits.MAX_MODULE_BYTES.val := by
    simp only [Slice.length] at ⊢
    omega
  have hecap : run.environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := he.2
    rw [hend] at this
    simpa using this
  have hdecoded := metadata.validate_env_with.accepted_erase visitor.metadataModuleVisitorInst
    run.environment run.region run.decodedPrefix run.environmentLength run.decoded run.decode_environment
  obtain ⟨henv, _⟩ := Module.Environment.accepted_entry_conditions _ _ _ hecap hdecoded
  have hsem := metadata.validate_env.semantic_spec run.environment
  rw [hdecoded] at hsem
  simp only [WP.spec_ok] at hsem
  obtain ⟨decls, hrep, hvalid, flags, _, _, before, hprefix, hspan⟩ := hsem
  have hwhole : run.environment.val = before := by
    rw [hend] at hspan
    simpa using hspan.suffix
  have hheader := stream.read_code_header.sound source state run.remaining.codeLength run.decodedPrefix.code
    run.remaining.entries code environment.val tail.val hsource hlen hrep.cache.imported_func_bound run.remaining.header_call
  have hstart : run.remaining.entries.val ≤ code.length := by
    rcases hheader with hempty | ⟨_, _, hb⟩
    · simp [hempty.1, hempty.2.1, Slice.length]
    · exact hb
  have hcodeLen : run.remaining.codeLength = Slice.len code := by
    apply UScalar.eq_of_val_eq
    exact hlen
  have hregion := hp.region id [] v .Environment run.region hv run.region_call
  have hdecodedTracks := hp.environment_preserves id [] run.environment run.region run.decoded
    run.decodedPrefix run.environmentLength run.decode_environment hregion
  have hconfigured := hp.environment id [] run.decoded run.decodedPrefix run.remaining.config run.remaining.configured
    hdecodedTracks run.remaining.configured_call
  have hsubmit := run.remaining.submit_call
  rw [hcodeLen] at hsubmit
  obtain ⟨history, nextId, hinv, hsubmitted⟩ := stream.submit_code_batches.sound source visitor Tracks hp
    state id run.decodedPrefix.code code run.remaining.entries run.remaining.config run.remaining.configured
    run.remaining.pending run.remaining.submitted environment.val tail.val hsource henv hcap hstart
    hconfigured hsubmit
  have hended := hp.code_end id history _ _ hsubmitted run.remaining.end_call
  have htailRegion := hp.region id history _ .Tail _ hended run.remaining.region_call
  have htailDecoded := hp.tail_preserves id history run.remaining.tailBytes 0#usize _ _ run.decodedPrefix.code
    run.remaining.tail run.remaining.decode_tail htailRegion
  have hentry : ∀ issued ∈ history, CodeEntry.Bounds issued.env := by
    intro issued hi
    have he := (hinv.issued issued hi).2.1
    simpa [he] using henv
  obtain ⟨_, _, hcompleted⟩ := Stream.Scheduler.drain_sound visitor Tracks hp id history
    run.remaining.decodedTail v' run.remaining.pending run.remaining.remaining htailDecoded hentry run.remaining.drain_call
  have hall : ∀ issued ∈ history, Stream.Scheduler.Completed issued := by
    intro issued hi
    rcases hinv.accounted issued hi with hpend | hdone
    · exact hcompleted issued hi (hinv.issued issued hi).1 hpend
    · exact hdone
  obtain ⟨codes, hcode, htyped⟩ := Stream.Scheduler.Partition.code hheader hinv.partition hall
  have htail := metadata.validate_tail_with.accepted_erase visitor.metadataModuleVisitorInst
    run.remaining.tailBytes 0#usize run.decodedPrefix.code run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have htailSem := metadata.validate_tail.spec run.remaining.tailBytes 0#usize run.decodedPrefix.code (by simp)
  rw [htail] at htailSem
  simp only [WP.spec_ok] at htailSem
  obtain ⟨⟨tailBytes, ht, hts⟩, hsegments, hdataCount⟩ := htailSem
  have htailWhole : run.remaining.tailBytes.val = tailBytes := by simpa using hts.suffix
  refine ⟨⟨run⟩, ?_, ?_⟩
  · rw [run.published]
    exact Module.Sound.assembled_regions hbytes (by simpa [← hwhole, heq] using hprefix)
      hrep hvalid flags hcode (by simpa [hrep.cache.defined_type_indices] using htyped) (by simpa [← htailWhole, hteq] using ht) hsegments hdataCount
  · have heLength := congrArg List.length heq
    have htLength := congrArg List.length hteq
    have hdLength := congrArg List.length hbytes
    simp only [List.length_append] at hdLength
    simp only [Slice.len_val, Slice.length] at he hc hm ⊢
    omega

end Itasca

end

/-! ## SplitComplete -/

section

/-!
# Code region splitter completeness

`stream.find_code_region.complete` shows that for an independently encoded module,
`stream.find_code_region` returns the environment, code and tail boundaries of its normalized
`Module.Layout`. The canonical split is at the code section (ID 10), or at the first later
section other than data count (ID 12), or at the end of the input. The helper lemmas show how the
scanning loop skips custom sections and the preceding known sections.
-/

open Aeneas Aeneas.Std

namespace Itasca
open Binary

theorem Stream.Split.body_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (hid : id.val ≤ 10 ∨ id.val = 12) :
    stream.find_code_region_loop.body data (Slice.len data) pos =
      .ok (if id = 10#u8 then .done (pos, last)
        else if last = Slice.len data then .done (last, last) else .cont last) := by
  obtain ⟨middle, count, hb, hd, hlast, hbound⟩ := h
  obtain ⟨hp, hbyte, hmiddle⟩ := hb.byte.single
  obtain ⟨len, hlen, hlenval⟩ := stream.read_len.complete data middle first count hd
  have hs : stream.find_code_region_loop.body data (Slice.len data) pos ⦃ r =>
      r = if id = 10#u8 then .done (pos, last)
        else if last = Slice.len data then .done (last, last) else .cont last ⦄ := by
    unfold stream.find_code_region_loop.body
    have hn : ¬ pos ≥ Slice.len data := by scalar_tac
    simp only [hn, ↓reduceIte]
    step
    by_cases hnid : id > metadata.SECTION_CODE
    · have hidCount : id = metadata.SECTION_DATA_COUNT := by
        apply UScalar.eq_of_val_eq
        simp only [metadata.SECTION_DATA_COUNT]
        simp only [metadata.SECTION_CODE] at hnid
        scalar_tac
      simp only [hnid, ↓reduceIte]
      simp only [hidCount, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      step
      have he : i = middle := by apply UScalar.eq_of_val_eq; omega
      subst i
      simp only [hlen, bind_ok]
      step
      step
      step
      have he : «end» = last := by apply UScalar.eq_of_val_eq; scalar_tac
      subst «end»
      simp only [metadata.SECTION_CODE]
      split <;> split <;> simp_all
    · simp only [hnid, ↓reduceIte]
      step
      have he : i = middle := by apply UScalar.eq_of_val_eq; omega
      subst i
      simp only [hlen, bind_ok]
      step
      step
      step
      have he : «end» = last := by apply UScalar.eq_of_val_eq; scalar_tac
      subst «end»
      simp only [metadata.SECTION_CODE]
      split <;> split <;> simp_all
  obtain ⟨r, hr, he⟩ := WP.spec_imp_exists hs
  exact hr.trans (congrArg Result.ok he)

theorem Stream.Split.loop_eof (data : Slice U8) :
    stream.find_code_region_loop data (Slice.len data) (Slice.len data) =
      .ok (Slice.len data, Slice.len data) := by
  rw [stream.find_code_region_loop, loop]
  simp [stream.find_code_region_loop.body]

theorem Stream.Split.skip_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (hid : id.val < 10 ∨ id.val = 12) :
    stream.find_code_region_loop data (Slice.len data) pos =
      stream.find_code_region_loop data (Slice.len data) last := by
  have hb := Stream.Split.body_section data pos first last id h (by omega)
  have hn : id ≠ 10#u8 := by scalar_tac
  simp only [hn, ↓reduceIte] at hb
  by_cases hend : last = Slice.len data
  · rw [hend, Stream.Split.loop_eof]
    rw [stream.find_code_region_loop, loop, hb]
    simp [hend]
  · unfold stream.find_code_region_loop
    rw [loop, hb]
    simp [hend]

private theorem split_code_section (data : Slice U8) (pos first last : Usize)
    (h : SectionHeader data pos 10#u8 first last) :
    stream.find_code_region_loop data (Slice.len data) pos = .ok (pos, last) := by
  rw [stream.find_code_region_loop, loop, Stream.Split.body_section data pos first last 10#u8 h (by decide)]
  simp

private theorem split_after_code (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (hid : 10 < id.val) (hnotCount : id.val ≠ 12) :
    stream.find_code_region_loop data (Slice.len data) pos = .ok (pos, pos) := by
  obtain ⟨_, _, hb, _, _, _⟩ := h
  obtain ⟨hp, hbyte, _⟩ := hb.byte.single
  have hs : stream.find_code_region_loop.body data (Slice.len data) pos ⦃ r =>
      r = .done (pos, pos) ⦄ := by
    unfold stream.find_code_region_loop.body
    have hn : ¬ pos ≥ Slice.len data := by scalar_tac
    simp only [hn, ↓reduceIte]
    step
    have hnid : id > metadata.SECTION_CODE := by simp [metadata.SECTION_CODE]; scalar_tac
    have hncount : id ≠ metadata.SECTION_DATA_COUNT := by
      intro he
      have hv := congrArg UScalar.val he
      simp only [metadata.SECTION_DATA_COUNT] at hv
      scalar_tac
    simp [hnid, hncount]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  rw [stream.find_code_region_loop, loop, hr]
  simp

/-- Adjacent independent section prefixes concatenate. -/
theorem Stream.CompleteRegions.Prefix.append {data first middle last}
    (left : Stream.CompleteRegions.Prefix data first middle)
    (right : Stream.CompleteRegions.Prefix data middle last) :
    Stream.CompleteRegions.Prefix data first last := by
  induction left with
  | empty => exact right
  | skip header before _ ih => exact .skip header before (ih right)

private theorem prefix_customs {data : Slice U8} {bytes : List U8}
    (h : CustomsEncoding bytes) {pos next : Usize} (hb : Body.Scalar.BytesAt data pos bytes next) :
    Stream.CompleteRegions.Prefix data pos next := by
  induction h generalizing pos with
  | nil => rw [hb.empty]; exact .empty _
  | cons hc _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨nm, payload, encodedName, _, hs⟩ := hc
    obtain ⟨content, hh, _⟩ := (show At
      (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = encodedName ++ payload))
      data pos () middle from ⟨_, hs, hfirst⟩).section_split
    exact .skip hh (by decide) (ih hrest)

private theorem prefix_chain {data : Slice U8} {raw n bytes}
    (h : Module.Environment.Chain raw n bytes ) {pos next : Usize}
    (hb : Body.Scalar.BytesAt data pos bytes next) :
    Stream.CompleteRegions.Prefix data pos next := by
  induction h generalizing pos with
  | done hc => exact prefix_customs hc hb
  | @step n id first rest hn hid hslot _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨customs, sec, hc, hs, he⟩ := hslot
    rw [he] at hfirst
    obtain ⟨afterCustoms, hcustoms, hsection⟩ := hfirst.split
    apply Stream.CompleteRegions.Prefix.append (prefix_customs hc hcustoms)
    rcases hs with ⟨_, rfl⟩ | hs
    · rw [← hsection.empty]
      exact ih hrest
    · obtain ⟨content, hh, _⟩ := (show
        At (SectionEncoding id (fun u bs => Module.Environment.Payload raw (sectionRank id).val u bs )) data afterCustoms () middle
        from ⟨_, hs, hsection⟩).section_split
      apply Stream.CompleteRegions.Prefix.skip hh (by
        have hrange := section_rank_prefix (id := id) (by omega) (by omega)
        omega)
      exact ih hrest

theorem Stream.Split.canonical_prefix {data : Slice U8} {decls next}
    (h : At (fun ds bs => Module.Environment.PrefixEncoding ds bs ) data 0#usize decls next) :
    Stream.CompleteRegions.Prefix data 8#usize next := by
  obtain ⟨bytes, hp, hb⟩ := h
  obtain ⟨suffix, hc, he⟩ := hp.chain [] []
  rw [he] at hb
  obtain ⟨middle, hmagic, hchain⟩ := hb.split
  have hm : middle = 8#usize := by
    apply UScalar.eq_of_val_eq
    simpa [magicVersion] using hmagic.length
  subst middle
  exact prefix_chain hc hchain

/-- A normalized independent module layout supplies canonical section boundaries. -/
theorem Module.Layout.canonical {data : Slice U8} {raw decls codePos tailPos}
    (h : Module.Layout data raw decls codePos tailPos ) :
    Stream.CompleteRegions.Boundaries data codePos tailPos := by
  refine ⟨Stream.Split.canonical_prefix h.environment, ?_⟩
  rcases h.code with hc | ⟨_, hsame, hstop⟩
  · obtain ⟨first, hh, _⟩ := hc.section_split
    exact .inl ⟨first, hh⟩
  · subst tailPos
    rcases hstop with heof | ⟨id, first, last, hh, hne⟩
    · have he : codePos = Slice.len data := by apply UScalar.eq_of_val_eq; simpa using heof
      exact .inr ⟨rfl, .inl he⟩
    · rcases h.stop with heof | ⟨id', first', last', hh', hge⟩
      · have hs := hh.span
        have he := congrArg UScalar.val heof
        simp only [Slice.len_val] at he
        omega
      · have he : id = id' ∧ first = first' ∧ last = last' := by
          have hread := (metadata.read_section_header.complete data codePos id first last hh).symm.trans
            (metadata.read_section_header.complete data codePos id' first' last' hh')
          simpa using hread
        have hid : id = 11#u8 := by
          rcases hge with hc | hd
          · exact False.elim (hne (he.1.trans hc))
          · exact he.1.trans hd
        exact .inr ⟨rfl, .inr ⟨id, first, last, hh, by simp [hid], by simp [hid]⟩⟩

/-- Scanning skips exactly the independently framed preceding sections. -/
theorem Stream.CompleteRegions.Prefix.computed {data start finish}
    (preceding : Stream.CompleteRegions.Prefix data start finish) :
    stream.find_code_region_loop data (Slice.len data) start =
      stream.find_code_region_loop data (Slice.len data) finish := by
  induction preceding with
  | empty => rfl
  | skip header before _ ih =>
    exact (Stream.Split.skip_section _ _ _ _ _ header before).trans ih

/-- The executable scanner implements the independent section boundaries. -/
theorem Stream.CompleteRegions.Boundaries.computed {data first last}
    (boundaries : Stream.CompleteRegions.Boundaries data first last) :
    stream.find_code_region data = .ok (first, last) := by
  simp only [stream.find_code_region, boundaries.preceding.computed]
  rcases boundaries.stop with ⟨content, header⟩ | ⟨rfl, stop⟩
  · exact split_code_section _ _ _ _ header
  · rcases stop with rfl | ⟨id, content, finish, header, later, notCount⟩
    · exact Stream.Split.loop_eof data
    · exact split_after_code _ _ _ _ _ header later notCount

/-- The scanner skips the independently encoded environment prefix. -/
theorem Stream.Split.skip_prefix {data : Slice U8} {decls next}
    (encoded : At (fun ds bs => Module.Environment.PrefixEncoding ds bs) data 0#usize decls next) :
    stream.find_code_region_loop data (Slice.len data) 8#usize =
      stream.find_code_region_loop data (Slice.len data) next :=
  (Stream.Split.canonical_prefix encoded).computed

/-- The scanner realizes the boundaries of an independently normalized module. -/
theorem stream.find_code_region.complete_layout {data : Slice U8} {raw decls codePos tailPos}
    (layout : Module.Layout data raw decls codePos tailPos) :
    stream.find_code_region data = .ok (codePos, tailPos) :=
  layout.canonical.computed

/-- Independent slice contents determine the concrete slice operation. -/
private theorem slice_computed {data region : Slice U8} {first last : Usize}
    (ordered : first.val ≤ last.val) (bounded : last.val ≤ data.length)
    (contents : region.val = data.val.slice first.val last.val) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨first, last⟩ = .ok region := by
  have post := core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
    ⟨first,last⟩ data (by scalar_tac) bounded
  obtain ⟨actual, called, value, _⟩ := WP.spec_imp_exists post
  have same : actual = region := by apply Slice.ext; exact value.trans contents.symm
  subst actual
  change core.slice.index.SliceIndexRangeUsizeSlice.index ⟨first,last⟩ data = .ok region
  exact called

/-- The extracted scanner and slice adapter realize the independent split. -/
theorem Stream.CompleteRegions.Split.computed {data regions}
    (split : Stream.CompleteRegions.Split data regions) :
    Stream.CompleteRegions.ComputedSplit data regions := by
  obtain ⟨first,last,boundaries,environment,code,tail⟩ := split
  have scanned := boundaries.computed
  obtain ⟨ordered,bounded⟩ := stream.find_code_region.bounds data first last scanned
  exact ⟨first,last,scanned,
    slice_computed (by simp) (by omega) environment,
    slice_computed ordered bounded code,
    slice_computed (by simpa using bounded) (by simp) tail⟩


end Itasca

end
