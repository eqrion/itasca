import Itasca.Stream.SubmissionTotal
import Itasca.Stream.InvariantRetirement

open Aeneas Aeneas.Std

namespace Itasca.StreamSubmission

variable {profile : ValidationProfile}

/-- Submission and polling return on reached scheduler states and preserve the
state predicate after successful callbacks. The issued environment is fixed. -/
structure CallbacksOn {V : Type} (visitor : stream.StreamingVisitor V)
    (env : metadata.Env) (invariant : Nat → V → Prop) (profile : ValidationProfile) : Prop where
  submit : ∀ v (issued : StreamBatch.Issued), invariant issued.first_func.val v → issued.env = env →
    issued.Bounded → CodeEntry.Bounds issued.env → issued.profile = profile →
    visitor.submit_code_batch v issued.seed ⦃ out => out.1 = .Ok () → invariant (issued.first_func.val + issued.num_funcs.val) out.2 ⦄
  poll : ∀ cursor, StreamRetirement.PollTotalOn visitor (invariant cursor)

/-- Successful submission retains both pending-vector and scheduler bounds. -/
def PostOn (invariant : Nat → V → Prop) (finish : Nat) (max : Usize) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok remaining, v) => remaining.length ≤ max.val ∧ invariant finish v
  | (.Err _, _) => True

/-- The loop continuation after its optional retirement, written as the extracted subexpression
so that both generated branches share one proof. -/
private theorem resume_on {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (codeLen : Usize) (config : stream.Config)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId num : Usize)
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant profile)
    (held : invariant func.val v)
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
            { module_id := moduleId, batch_id := batchId, profile := profile, env := env, code := bytes,
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
      | .done result => PostOn invariant num.val config.max_batches result
      | .cont (v', pending', pos', func', batchId') =>
        (invariant func'.val v' ∧ StreamSubmission.Invariant codeLen num config.max_batches pending' pos' func' batchId') ∧
          num.val - func'.val < num.val - func.val ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (stream.get_next_batch.spec source state codeLen pos func num config.batch_bytes hs hcap hpos hfunc)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, PostOn]
  | Ok pair =>
    obtain ⟨finish, next⟩ := pair
    obtain ⟨hposnext, hfinish, hnextmore, hnextbound⟩ := hp
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨r, hread, hreadp⟩ := WP.spec_imp_exists
      (stream.read_exact.spec source state pos finish (by omega) (hs.code_returns _ _))
    rw [hread]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, PostOn]
    | Ok bytes =>
      have hlen := hreadp.2
      have hnumMax : num.val ≤ Usize.max := by scalar_tac
      simp
      step
      step
      let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count, profile⟩
      have hb : issued.Bounded := by
        dsimp [issued, StreamBatch.Issued.Bounded]
        scalar_tac
      obtain ⟨⟨reply, v'⟩, hsubmit, retained⟩ := WP.spec_imp_exists (hv.submit v issued held rfl hb henv rfl)
      dsimp only [issued, StreamBatch.Issued.seed] at hsubmit
      rw [hsubmit]
      cases reply with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, PostOn]
      | Ok u =>
        cases u
        simp
        step
        simp only [Invariant]
        have retainedNext : invariant next.val v' := by
          have h := retained rfl
          dsimp [issued] at h
          have eq : func.val + count.val = next.val := by scalar_tac
          simpa only [eq] using h
        refine ⟨retainedNext, ?_⟩
        scalar_tac

end Itasca.StreamSubmission

namespace Itasca

variable {profile : ValidationProfile}

private theorem submit_body_total_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen : Usize) (config : stream.Config) (num : Usize)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant profile)
    (held : invariant func.val v)
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      codeLen config num v pending pos func batchId ⦃ out => match out with
      | .done result => StreamSubmission.PostOn invariant num.val config.max_batches result
      | .cont (v', pending', pos', func', batchId') =>
        (invariant func'.val v' ∧ StreamSubmission.Invariant codeLen num config.max_batches pending' pos' func' batchId') ∧
          num.val - func'.val < num.val - func.val ⦄ := by
  obtain ⟨hpos, hfunc, hbatch, hpending, hmax⟩ := hinv
  unfold stream.submit_code_batches_loop.body
  by_cases hmore : func < num
  · rw [if_pos hmore]
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull]
      obtain ⟨⟨r, v', remaining⟩, hr, hp, retained⟩ := WP.spec_imp_exists
        (stream.retire_code_batch.spec_on visitor (invariant func.val) moduleId v pending (hv.poll func.val) held)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          StreamSubmission.PostOn]
      | Ok u =>
        cases u
        obtain ⟨batch, _, _, _, hperm⟩ := hp
        have hlen : remaining.length + 1 = pending.length := by
          simpa [alloc.vec.Vec.length] using hperm.length_eq
        have hresume :=
          (StreamSubmission.resume_on source visitor state moduleId env codeLen config v' remaining
            pos func batchId num hs invariant hv (retained rfl) henv hnum hcap hpos (by scalar_tac) hbatch
            (by omega) (by scalar_tac))
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
        convert hresume using 1 <;> rfl
    · rw [if_neg hfull]
      exact StreamSubmission.resume_on source visitor state moduleId env codeLen config v pending
        pos func batchId num hs invariant hv held henv hnum hcap hpos (by scalar_tac) hbatch hpending (by scalar_tac)
  · rw [if_neg hmore]
    split
    · simp [StreamSubmission.PostOn]
    · have eq : func.val = num.val := by scalar_tac
      have last : invariant num.val v := by simpa only [eq] using held
      simpa [StreamSubmission.PostOn] using And.intro hmax last

/-- Submission terminates because each framed batch contains at least one function. The pending
vector stays within the configured maximum. -/
theorem stream.submit_code_batches_loop.spec_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen : Usize) (config : stream.Config) (v : V)
    (pending : alloc.vec.Vec Usize) (pos func batchId num : Usize)
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant profile)
    (held : invariant func.val v)
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      codeLen config v pending pos func batchId num ⦃ StreamSubmission.PostOn invariant num.val config.max_batches ⦄ := by
  unfold stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => num.val - s.2.2.2.1.val)
    (fun s => invariant s.2.2.2.1.val s.1 ∧ StreamSubmission.Invariant codeLen num config.max_batches s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (submit_body_total_on source visitor moduleId state env codeLen config num
      v' pending' pos' func' batchId' hs invariant hv h.1 henv hnum hcap h.2)
    intro out hout
    cases out with
    | done result => exact hout
    | cont next => rcases next with ⟨_, _, _, _, _⟩; exact hout
  · exact ⟨held, hinv⟩

/-- `stream.submit_code_batches` returns and keeps its pending vector within the configured
maximum, when the source and scheduler callbacks return. -/
@[step]
theorem stream.submit_code_batches.spec_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen pos : Usize) (config : stream.Config) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant profile)
    (held : invariant 0 v)
    (henv : CodeEntry.Bounds env) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) :
    stream.submit_code_batches source visitor moduleId profile state env codeLen pos config v
      ⦃ StreamSubmission.PostOn invariant env.func_type_indices.val.length config.max_batches ⦄ := by
  unfold stream.submit_code_batches
  apply stream.submit_code_batches_loop.spec_on source visitor moduleId state env codeLen config v
    (alloc.vec.Vec.new Usize) pos 0#usize 0#usize (alloc.vec.Vec.len env.func_type_indices)
    hs invariant hv held henv rfl hcap
  exact ⟨hpos, by simp, by simp, by simp, by simp⟩

end Itasca
