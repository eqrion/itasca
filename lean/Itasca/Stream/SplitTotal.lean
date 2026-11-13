import Itasca.Stream.Header
import Itasca.Module.Code.FuncTyping
import Itasca.Module.Custom.Trace
import Itasca.Stream.Source

/-!
Sections, each formerly its own module: FramingTotal, SubmissionTotal, DriverTotal, SplitTotal.
-/

/-! ## FramingTotal -/

section

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

end Itasca

end

/-! ## SubmissionTotal -/

section

/-!
# Submission termination

Termination of `stream.submit_code_batches` and its loop, which frame code batches, issue them to
the scheduler through `submit_code_batch`, and retire a batch whenever the pending vector is full.
`StreamSubmission.Invariant` bounds the cursors and the pending vector, and every iteration
advances the function cursor. Termination needs the source and scheduler callbacks to return
(`StreamSource.CallbacksTotal`, `StreamScheduler.CallbacksTotal`).
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSubmission
/-- Both outstanding IDs and issued batch IDs are bounded by the function
cursor; every successful submission advances that cursor. -/
def Invariant (codeLen num max : Usize) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) : Prop :=
  pos.val ≤ codeLen.val ∧ func.val ≤ num.val ∧ batchId.val ≤ func.val ∧
    pending.length ≤ batchId.val ∧ pending.length ≤ max.val

/-- A returned pending vector stays within the configured maximum. Errors are unconstrained. -/
def Post (max : Usize) : (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok remaining, _) => remaining.length ≤ max.val
  | (.Err _, _) => True

/-- The loop continuation after its optional retirement, written as the extracted subexpression
so that both generated branches share one proof. -/
private theorem resume {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (codeLen : Usize) (config : stream.Config)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId num : Usize)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) (hfunc : func.val < num.val)
    (hbatch : batchId.val ≤ func.val) (hpending : pending.length ≤ batchId.val)
    (hroom : pending.length < config.max_batches.val) :
    (do
      let r ← stream.get_next_batch source state codeLen pos func num config.batch_bytes
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
        Result.ok (ControlFlow.done (r1, v))) ⦃ out => match out with
      | .done result => Post config.max_batches result
      | .cont (_, pending', pos', func', batchId') =>
        Invariant codeLen num config.max_batches pending' pos' func' batchId' ∧
          num.val - func'.val < num.val - func.val ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (stream.get_next_batch.spec source state codeLen pos func num config.batch_bytes hs hcap hpos hfunc)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Post]
  | Ok pair =>
    obtain ⟨finish, next⟩ := pair
    obtain ⟨hposnext, hfinish, hnextmore, hnextbound⟩ := hp
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨r, hread, hreadp⟩ := WP.spec_imp_exists
      (stream.read_exact.spec source state pos finish (by omega) (hs.code_returns _ _))
    rw [hread]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Post]
    | Ok bytes =>
      have hlen := hreadp.2
      have hnumMax : num.val ≤ Usize.max := by scalar_tac
      simp
      step
      step
      let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count⟩
      have hb : issued.Bounded := by
        dsimp [issued, StreamBatch.Issued.Bounded]
        scalar_tac
      obtain ⟨⟨reply, v'⟩, hsubmit⟩ := hv.submit v issued hb henv
      dsimp only [issued, StreamBatch.Issued.seed] at hsubmit
      rw [hsubmit]
      cases reply with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Post]
      | Ok u =>
        cases u
        simp
        step
        simp only [Invariant]
        scalar_tac

end Itasca.StreamSubmission

namespace Itasca
private theorem submit_body_total {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen : Usize) (config : stream.Config) (num : Usize)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      codeLen config num v pending pos func batchId ⦃ out => match out with
      | .done result => StreamSubmission.Post config.max_batches result
      | .cont (_, pending', pos', func', batchId') =>
        StreamSubmission.Invariant codeLen num config.max_batches pending' pos' func' batchId' ∧
          num.val - func'.val < num.val - func.val ⦄ := by
  obtain ⟨hpos, hfunc, hbatch, hpending, hmax⟩ := hinv
  unfold stream.submit_code_batches_loop.body
  by_cases hmore : func < num
  · rw [if_pos hmore]
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull]
      obtain ⟨⟨r, v', remaining⟩, hr, hp⟩ := WP.spec_imp_exists
        (stream.retire_code_batch.spec visitor moduleId v pending (hv.poll v))
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          StreamSubmission.Post]
      | Ok u =>
        cases u
        obtain ⟨batch, _, _, _, hperm⟩ := hp
        have hlen : remaining.length + 1 = pending.length := by
          simpa [alloc.vec.Vec.length] using hperm.length_eq
        have hresume :=
          (StreamSubmission.resume source visitor state moduleId env codeLen config v' remaining
            pos func batchId num hs hv henv hnum hcap hpos (by scalar_tac) hbatch
            (by omega) (by scalar_tac))
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
        convert hresume using 1 <;> rfl
    · rw [if_neg hfull]
      exact StreamSubmission.resume source visitor state moduleId env codeLen config v pending
        pos func batchId num hs hv henv hnum hcap hpos (by scalar_tac) hbatch hpending (by scalar_tac)
  · rw [if_neg hmore]
    split
    · simp [StreamSubmission.Post]
    · simpa [StreamSubmission.Post] using hmax

/-- Submission terminates because each framed batch contains at least one function. The pending
vector stays within the configured maximum. -/
theorem stream.submit_code_batches_loop.spec {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen : Usize) (config : stream.Config) (v : V)
    (pending : alloc.vec.Vec Usize) (pos func batchId num : Usize)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      codeLen config v pending pos func batchId num ⦃ StreamSubmission.Post config.max_batches ⦄ := by
  unfold stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => num.val - s.2.2.2.1.val)
    (fun s => StreamSubmission.Invariant codeLen num config.max_batches s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (submit_body_total source visitor moduleId state env codeLen config num
      v' pending' pos' func' batchId' hs hv henv hnum hcap h)
    intro out hout
    cases out with
    | done result => exact hout
    | cont next => rcases next with ⟨_, _, _, _, _⟩; exact hout
  · exact hinv

/-- `stream.submit_code_batches` returns and keeps its pending vector within the configured
maximum, when the source and scheduler callbacks return. -/
@[step]
theorem stream.submit_code_batches.spec {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen pos : Usize) (config : stream.Config) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) :
    stream.submit_code_batches source visitor moduleId state env codeLen pos config v
      ⦃ StreamSubmission.Post config.max_batches ⦄ := by
  unfold stream.submit_code_batches
  apply stream.submit_code_batches_loop.spec source visitor moduleId state env codeLen config v
    (alloc.vec.Vec.new Usize) pos 0#usize 0#usize (alloc.vec.Vec.len env.func_type_indices)
    hs hv henv rfl hcap
  exact ⟨hpos, by simp, by simp, by simp, by simp⟩

theorem stream.submit_code_batches.total {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen pos : Usize) (config : stream.Config) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) :
    ∃ r, stream.submit_code_batches source visitor moduleId state env codeLen pos config v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.submit_code_batches.spec source visitor moduleId state env codeLen pos config v hs hv henv hcap hpos)
  exact ⟨r, hr⟩

end Itasca

end

/-! ## DriverTotal -/

section

/-!
# Streaming driver termination

`stream.validate_streaming.total_core`: on arbitrary bytes, `stream.validate_streaming`
returns success or an error whenever the source and scheduler callbacks return
(`StreamSource.CallbacksTotal`, `StreamScheduler.CallbacksTotal`). Coherence, availability and
worker provenance are not premises. `stream.validate_remaining.total_spec` covers the phases after
the environment. `Itasca/Results/Stream` states the public `profile_total`.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- A checked header declares no more entries than the code region has bytes. -/
theorem HeaderChecked.entries_le {S : Type} {source : stream.Source S} {state : S}
    {codeLen : Usize} {env : metadata.Env} {entries : Usize}
    (h : HeaderChecked source state codeLen env entries) : entries.val ≤ codeLen.val := by
  rcases h with ⟨rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hp, _⟩
  · simp
  · exact hp

end Itasca.StreamFraming

namespace Itasca
/-- After a decoded environment, all remaining phases return an ordinary result when the source
and visitor callbacks return. Worker provenance is not needed. -/
theorem stream.validate_remaining.total_spec {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (envLen : Usize) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) :
    stream.validate_remaining source visitor moduleId state env envLen v ⦃ _ => True ⦄ := by
  obtain ⟨codeLen, hlen⟩ := hs.code_len_returns
  unfold stream.validate_remaining
  rw [hlen]
  simp only [bind_ok]
  obtain ⟨r, hsum, hsp⟩ := WP.spec_imp_exists (limits.add_offset.spec envLen codeLen)
  rw [hsum]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok beforeTail =>
    have hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val := by omega
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨r, hheader, hhp⟩ := WP.spec_imp_exists
      (stream.read_code_header.spec source state codeLen env (fun _ => hs.code_returns _ _))
    rw [hheader]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok entries =>
      simp
      obtain ⟨⟨r, v1⟩, hready⟩ := hv.environment v env
      rw [hready]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok config =>
        simp
        split
        · simp
        · split
          · simp
          · obtain ⟨r, hsubmit⟩ := stream.submit_code_batches.total source visitor moduleId state
              env codeLen entries config v1 hs hv henv hcap hhp.entries_le
            rw [hsubmit]
            obtain ⟨r, v2⟩ := r
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pending =>
              simp
              obtain ⟨⟨r, v3⟩, hcodeEnd⟩ := hv.code_end v2
              rw [hcodeEnd]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                cases u
                simp
                obtain ⟨r, htail⟩ := hs.tail_returns
                rw [htail]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok bytes =>
                  simp
                  obtain ⟨r, hadd⟩ := limits.add_offset.total beforeTail (Slice.len bytes)
                  rw [hadd]
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok whole =>
                    simp
                    obtain ⟨v4, hregion⟩ := hv.region v3 stream.Region.Tail
                    rw [hregion]
                    simp only [bind_ok]
                    obtain ⟨⟨r, v5⟩, hparsed, _⟩ := WP.spec_imp_exists
                      (metadata.validate_tail_with.spec visitor.metadataModuleVisitorInst hv.custom
                        bytes 0#usize env v4 (by simp) )
                    rw [hparsed]
                    cases r with
                    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                    | Ok tail =>
                      simp
                      obtain ⟨⟨r, v6⟩, hready⟩ := hv.tail_ready v5 tail
                      rw [hready]
                      cases r with
                      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                      | Ok u =>
                        cases u
                        simp
                        obtain ⟨⟨r, v7, remaining⟩, hdrain⟩ :=
                          stream.retire_all_code_batches.total visitor moduleId v6 pending hv.poll
                        rw [hdrain]
                        simp

/-- `stream.validate_remaining` returns an ordinary result under returning callbacks. -/
theorem stream.validate_remaining.total {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (envLen : Usize) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) :
    ∃ r, stream.validate_remaining source visitor moduleId state env envLen v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.validate_remaining.total_spec source visitor moduleId state env envLen v hs hv henv)
  exact ⟨r, hr⟩

/-- `stream.validate_streaming` returns success or an error on arbitrary bytes when the source and
scheduler callbacks return. Neither successful batches, source coherence nor scheduler provenance
is a termination premise. -/
theorem stream.validate_streaming.total_core {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V) (storage : metadata.Env)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor ) :
    ∃ r, stream.validate_streaming source visitor moduleId state v storage = .ok r := by
  have hspec : stream.validate_streaming source visitor moduleId state v storage ⦃ _ => True ⦄ := by
    unfold stream.validate_streaming
    obtain ⟨r, hread⟩ := hs.environment_returns
    rw [hread]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok bytes =>
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨r, hlen, hlenp⟩ := WP.spec_imp_exists (limits.add_offset.spec 0#usize (Slice.len bytes))
      rw [hlen]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok envLen =>
        have hsize : bytes.length ≤ limits.MAX_MODULE_BYTES.val := by scalar_tac
        simp
        obtain ⟨v1, hregion⟩ := hv.region v stream.Region.Environment
        rw [hregion]
        simp only [bind_ok]
        obtain ⟨⟨r, v2⟩, hparsed, _⟩ := WP.spec_imp_exists
          (metadata.validate_env_with.profile_spec visitor.metadataModuleVisitorInst hv.custom bytes v1)
        rw [hparsed]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨env, envEnd⟩ := pair
          have herase := metadata.validate_env_with.accepted_erase
            visitor.metadataModuleVisitorInst bytes v1 env envEnd v2 hparsed
          have henv := (ModuleEnv.profile_accepted_entry_conditions bytes env envEnd hsize herase).1
          simp
          split
          · obtain ⟨⟨r, v3⟩, hr⟩ := stream.validate_remaining.total source visitor moduleId state
              env envLen v2 hs hv henv
            rw [hr]
            simp
          · simp
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists hspec
  exact ⟨r, hr⟩

end Itasca

end

/-! ## SplitTotal -/

section

/-!
# Code region splitter termination

Termination and bounds of `stream.find_code_region`, which scans the section headers of a
contiguous module and returns the offsets that split it into environment, code and tail regions.
`stream.find_code_region.slices` shows that the three slices are safe and concatenate to the
whole input, whether or not it is a valid module. The canonical split is characterized in
`Stream/SplitComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The splitter loop returns on every buffer, including short and malformed ones. Its output
describes three adjacent in-bounds regions. -/
theorem stream.find_code_region_loop.spec (bytes : Slice U8) (pos : Usize) :
    stream.find_code_region_loop bytes (Slice.len bytes) pos ⦃ result =>
      result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  unfold stream.find_code_region_loop
  apply loop.spec_decr_nat (fun pos => bytes.length - pos.val) (fun _ => True)
  · intro cursor _
    unfold stream.find_code_region_loop.body
    split
    · simp
    · rename_i hcursor
      have hcursor' : cursor.val < bytes.length := by scalar_tac
      step
      split
      · split
        · simp; scalar_tac
        · step
          obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_len.spec bytes i)
          rw [hr]
          cases r with
          | Err e =>
            simp only [bind_ok]
            split <;> simp_all
          | Ok p =>
            obtain ⟨size, contents⟩ := p
            obtain ⟨_, _, hd⟩ := hp
            have hprogress := hd.span.1
            have hbound := hd.span.2.2
            simp only [bind_ok]
            step*
            scalar_tac
      · step
        obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_len.spec bytes i)
        rw [hr]
        cases r with
        | Err e =>
          simp only [bind_ok]
          split <;> simp_all
          scalar_tac
        | Ok p =>
          obtain ⟨size, contents⟩ := p
          obtain ⟨_, _, hd⟩ := hp
          have hprogress := hd.span.1
          have hbound := hd.span.2.2
          simp only [bind_ok]
          step* <;> scalar_tac
  · trivial

/-- `stream.find_code_region` returns on every buffer with ordered in-bounds offsets. -/
@[step]
theorem stream.find_code_region.spec (bytes : Slice U8) :
    stream.find_code_region bytes ⦃ result =>
      result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  simpa [stream.find_code_region] using
    stream.find_code_region_loop.spec bytes 8#usize

theorem stream.find_code_region.bounds (bytes : Slice U8) (first last : Usize)
    (h : stream.find_code_region bytes = .ok (first, last)) :
    first.val ≤ last.val ∧ last.val ≤ bytes.length := by
  have hs := stream.find_code_region.spec bytes
  simpa [h] using hs

/-- The slice operations at the split boundaries are safe and the resulting regions concatenate to
the input, whether or not the input is a valid module. -/
theorem stream.find_code_region.slices (bytes : Slice U8) (first last : Usize)
    (h : stream.find_code_region bytes = .ok (first, last)) :
    ∃ environment code tail : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨0#usize, first⟩ = .ok environment ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨first, last⟩ = .ok code ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨last, Slice.len bytes⟩ = .ok tail ∧
      bytes.val = environment.val ++ code.val ++ tail.val := by
  obtain ⟨hfirst, hlast⟩ := stream.find_code_region.bounds bytes first last h
  have slice_spec (start finish : Usize) (hs : start.val ≤ finish.val)
      (hf : finish.val ≤ bytes.length) :
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨start, finish⟩ ⦃ region =>
          Wasm1.BytesAt bytes start region.val finish ⦄ := by
    step
    apply Wasm1.BytesAt.of_slice_view hs hf
    assumption
  obtain ⟨environment, he, heSpan⟩ := WP.spec_imp_exists
    (slice_spec 0#usize first (by simp) (by omega))
  obtain ⟨code, hc, hcSpan⟩ := WP.spec_imp_exists (slice_spec first last hfirst hlast)
  obtain ⟨tail, ht, htSpan⟩ := WP.spec_imp_exists
    (slice_spec last (Slice.len bytes) (by simpa using hlast) (by simp))
  exact ⟨environment, code, tail, he, hc, ht,
    by simpa using ((heSpan.append hcSpan).append htSpan).suffix⟩

end Itasca

end
