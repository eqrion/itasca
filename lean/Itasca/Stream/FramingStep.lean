import Itasca.Support.Result
import Itasca.Stream.FramingTotal

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- A continuing framing step either stops before taking another entry, or
retains the exact returned view, decoded length and consecutive boundaries. -/
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

/-- The exact extracted loop body preserves arithmetic and records each
consumed declared extent, under a return premise only for its reached read. -/
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
