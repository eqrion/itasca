import Itasca.Stream.Header

/-!
# Batch framing termination

Termination of `stream.get_next_batch` and its loop `stream.get_next_batch_loop`, which frame code
entries until the byte threshold is reached or the entries run out. `StreamFraming.BatchInvariant`
holds along the loop and `StreamFraming.BatchPost` states what a successful framing returns: a
nonempty range of entries ending within the code region. Termination needs the source callbacks to
return (`StreamSource.CallbacksTotal`) and the code region to respect the module cap.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- Arithmetic facts maintained by the actual batch-framing loop. The byte
budget counts declared entry contents, including locals, but not size prefixes. -/
def BatchInvariant (codeLen start first num threshold : Usize)
    (pos func bytes : Usize) (done : Bool) : Prop :=
  start.val ≤ pos.val ∧ pos.val ≤ codeLen.val ∧
  first.val ≤ func.val ∧ func.val ≤ num.val ∧ bytes.val ≤ pos.val - start.val ∧
  (func = first → pos = start ∧ bytes = 0#usize ∧ done = false) ∧
  (done = false → func ≠ first → bytes.val < threshold.val)

/-- A successful framing returns the end offset of a nonempty batch and the index after its last
entry. Errors are unconstrained. -/
def BatchPost (codeLen start first num : Usize) :
    core.result.Result (Usize × Usize) error.Error → Prop
  | .Ok (finish, next) => start.val < finish.val ∧ finish.val ≤ codeLen.val ∧
      first.val < next.val ∧ next.val ≤ num.val
  | .Err _ => True

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

/-- The framing loop returns, and its result satisfies `StreamFraming.BatchPost`, from any state
satisfying `StreamFraming.BatchInvariant`. -/
theorem stream.get_next_batch_loop.total_spec {S : Type} (source : stream.Source S) (state : S)
    (codeLen start first num threshold pos func bytes : Usize) (done : Bool)
    (htotal : StreamSource.CallbacksTotal source state)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : StreamFraming.BatchInvariant codeLen start first num threshold pos func bytes done)
    (hprogress : first.val < func.val → start.val < pos.val) :
    stream.get_next_batch_loop source state codeLen first num threshold pos func bytes done
      ⦃ StreamFraming.BatchPost codeLen start first num ⦄ := by
  unfold stream.get_next_batch_loop
  apply loop.spec_decr_nat
    (fun s => 2 * (num.val - s.2.1.val) + if s.2.2.2 then 0 else 1)
    (fun s => StreamFraming.BatchInvariant codeLen start first num threshold s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
      (first.val < s.2.1.val → start.val < s.1.val))
  · rintro ⟨q, i, b, stopped⟩ ⟨hq, hprogress⟩
    obtain ⟨hstart, hq, hfirst, hi, hb, hinitial, hbudget⟩ := hq
    dsimp only at hstart hq hfirst hi hb hinitial hbudget hprogress
    unfold stream.get_next_batch_loop.body
    dsimp only
    split
    · rename_i himore
      split
      · rename_i hstop
        have hne : i ≠ first := by intro he; have := (hinitial he).2.2; simp_all
        have hlt : first.val < i.val := by
          have : first.val ≠ i.val := by intro he; apply hne; exact UScalar.eq_of_val_eq he.symm
          omega
        simpa [StreamFraming.BatchPost] using ⟨hprogress hlt, hq, hlt, hi⟩
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
          (core.cmp.impls.OrdUsize.min codeLen need) horder (htotal.code_returns _ _))
        rw [hr]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost]
        | Ok view =>
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨r, hl, hlp⟩ := WP.spec_imp_exists (stream.read_len.spec view 0#usize)
          rw [hl]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost]
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
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost]
              | Ok content =>
                simp
                obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
                rw [hf]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost]
                | Ok finish =>
                  simp
                  split
                  · simp [StreamFraming.BatchPost]
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
                    simpa [and_assoc] using ha
            · rename_i hnotequal
              have hne : i ≠ first := by intro he; simp [he] at hnotequal
              have hbbound := hbudget hfalse hne
              step
              split
              · simp only [WP.spec_ok, StreamFraming.BatchInvariant]
                refine ⟨⟨hstart, hq, hfirst, hi, hb, ?_, ?_⟩, hprogress, ?_⟩
                · intro he; exact False.elim (hne he)
                · intro he; cases he
                · simp
              · obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec q prefixLen)
                rw [hc]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost]
                | Ok content =>
                  simp
                  obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
                  rw [hf]
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StreamFraming.BatchPost]
                  | Ok finish =>
                    simp
                    split
                    · simp [StreamFraming.BatchPost]
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
                      simpa [and_assoc] using ha
    · rename_i hstop
      have hdone : i.val = num.val := by scalar_tac
      simpa [StreamFraming.BatchPost] using ⟨hprogress (by omega), hq, (by omega : first.val < i.val), hi⟩
  · exact ⟨hinv, hprogress⟩

/-- `stream.get_next_batch` returns and satisfies `StreamFraming.BatchPost` when the source
callbacks return and the code region respects the module cap. -/
theorem stream.get_next_batch.spec {S : Type} (source : stream.Source S) (state : S)
    (codeLen start first num threshold : Usize)
    (htotal : StreamSource.CallbacksTotal source state)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hstart : start.val ≤ codeLen.val) (hmore : first.val < num.val) :
    stream.get_next_batch source state codeLen start first num threshold
      ⦃ StreamFraming.BatchPost codeLen start first num ⦄ := by
  apply stream.get_next_batch_loop.total_spec source state codeLen start first num threshold
    start first 0#usize false htotal hcap hmore
  · simp [StreamFraming.BatchInvariant, hstart]
    omega
  · omega

theorem stream.get_next_batch.total {S : Type} (source : stream.Source S) (state : S)
    (codeLen start first num threshold : Usize)
    (htotal : StreamSource.CallbacksTotal source state)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hstart : start.val ≤ codeLen.val) (hmore : first.val < num.val) :
    ∃ r, stream.get_next_batch source state codeLen start first num threshold = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.get_next_batch.spec source state codeLen start first num threshold htotal hcap hstart hmore)
  exact ⟨r, hr⟩

end Itasca
