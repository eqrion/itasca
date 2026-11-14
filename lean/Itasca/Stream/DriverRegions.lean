import Itasca.Stream.SplitTotal
import Itasca.Stream.InvariantRetirement
import Itasca.Module.Custom.Trace
import Itasca.Module.Code.Framing
import Itasca.Stream.Source
import Itasca.Stream.Header
import Itasca.Contracts
import Itasca.Stream.SplitComplete
import Itasca.Module.Env.Complete
import Itasca.Module.Elab.Requirements
import Itasca.Module.Layout
import Itasca.Module.Sections.TailComplete
import Itasca.Module.Code.FuncTyping

/-!
Sections, each formerly its own module: InvariantSubmission, InvariantDriver, ReachedBatch, SchedulerComplete, HeaderComplete, DriverRegions.
-/

/-! ## InvariantSubmission -/

section

open Aeneas Aeneas.Std

namespace Itasca.StreamSubmission
/-- Submission and polling return on reached scheduler states and preserve the
state predicate after successful callbacks. The issued environment is fixed. -/
structure CallbacksOn {V : Type} (visitor : stream.StreamingVisitor V)
    (env : metadata.Env) (invariant : Nat → V → Prop) : Prop where
  submit : ∀ v (issued : StreamBatch.Issued), invariant issued.first_func.val v → issued.env = env →
    issued.Bounded → CodeEntry.Bounds issued.env →
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
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant )
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
      let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count⟩
      have hb : issued.Bounded := by
        dsimp [issued, StreamBatch.Issued.Bounded]
        scalar_tac
      obtain ⟨⟨reply, v'⟩, hsubmit, retained⟩ := WP.spec_imp_exists (hv.submit v issued held rfl hb henv)
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
private theorem submit_body_total_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (codeLen : Usize) (config : stream.Config) (num : Usize)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant )
    (held : invariant func.val v)
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId state env.types env.imports
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
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant )
    (held : invariant func.val v)
    (henv : CodeEntry.Bounds env) (hnum : num.val = env.func_type_indices.val.length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
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
    (hs : StreamSource.CallbacksTotal source state) (invariant : Nat → V → Prop) (hv : StreamSubmission.CallbacksOn visitor env invariant )
    (held : invariant 0 v)
    (henv : CodeEntry.Bounds env) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) :
    stream.submit_code_batches source visitor moduleId state env codeLen pos config v
      ⦃ StreamSubmission.PostOn invariant env.func_type_indices.val.length config.max_batches ⦄ := by
  unfold stream.submit_code_batches
  apply stream.submit_code_batches_loop.spec_on source visitor moduleId state env codeLen config v
    (alloc.vec.Vec.new Usize) pos 0#usize 0#usize (alloc.vec.Vec.len env.func_type_indices)
    hs invariant hv held henv rfl hcap
  exact ⟨hpos, by simp, by simp, by simp, by simp⟩

end Itasca

end

/-! ## InvariantDriver -/

section

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

/-- Reachable scheduler phases. Only custom-section hooks are globally total;
compilation callbacks are required on the states reached after environment setup. -/
structure CallbacksOn {V : Type} (visitor : stream.StreamingVisitor V)
    (pre : V → Prop) (ready : metadata.Env → Nat → V → Prop)
    (admissible : metadata.Env → Prop) : Prop where
  custom : ModuleTail.HooksTotal visitor.metadataModuleVisitorInst
  custom_pre : ModuleTail.PreservesInvariant visitor.metadataModuleVisitorInst pre
  custom_ready : ∀ env cursor, ModuleTail.PreservesInvariant visitor.metadataModuleVisitorInst (ready env cursor)
  region_pre : ∀ v region, pre v → visitor.custom_region v region ⦃ pre ⦄
  region_ready : ∀ env cursor v region, ready env cursor v → visitor.custom_region v region ⦃ ready env cursor ⦄
  environment : ∀ v env, pre v → admissible env → CodeEntry.Bounds env →
    visitor.environment_ready v env ⦃ out => ∀ config, out.1 = .Ok config → ready env 0 out.2 ⦄
  batches : ∀ env, StreamSubmission.CallbacksOn visitor env (ready env)
  code_end : ∀ env v, ready env env.func_type_indices.val.length v → visitor.code_end v ⦃ out => out.1 = .Ok () → ready env env.func_type_indices.val.length out.2 ⦄
  tail_ready : ∀ env v tail, ready env env.func_type_indices.val.length v →
    visitor.tail_ready v tail ⦃ out => out.1 = .Ok () → ready env env.func_type_indices.val.length out.2 ⦄

end Itasca.StreamScheduler

namespace Itasca
/-- After a decoded environment, returning callbacks on reached states suffice.
No successful batch or worker-provenance premise is used. -/
theorem stream.validate_remaining.spec_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (envLen : Usize) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (pre : V → Prop) (ready : metadata.Env → Nat → V → Prop) (admissible : metadata.Env → Prop)
    (hv : StreamScheduler.CallbacksOn visitor pre ready admissible ) (held : pre v)
    (henv : CodeEntry.Bounds env) (admitted : admissible env) :
    stream.validate_remaining source visitor moduleId state env envLen v ⦃ out => out.1 = .Ok () → ready env env.func_type_indices.val.length out.2 ⦄ := by
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
      obtain ⟨⟨r, v1⟩, hready, retained1⟩ := WP.spec_imp_exists (hv.environment v env held admitted henv)
      rw [hready]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok config =>
        simp
        split
        · simp
        · split
          · simp
          · obtain ⟨r, hsubmit, retained2⟩ := WP.spec_imp_exists (stream.submit_code_batches.spec_on source visitor moduleId state
              env codeLen entries config v1 hs (ready env) (hv.batches env) (retained1 config rfl) henv hcap hhp.entries_le)
            rw [hsubmit]
            obtain ⟨r, v2⟩ := r
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pending =>
              simp
              obtain ⟨⟨r, v3⟩, hcodeEnd, retained3⟩ := WP.spec_imp_exists (hv.code_end env v2 retained2.2)
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
                    obtain ⟨v4, hregion, retained4⟩ := WP.spec_imp_exists (hv.region_ready env env.func_type_indices.val.length v3 stream.Region.Tail (retained3 rfl))
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
                      have retained5 := metadata.validate_tail_with.accepted_invariant _ (ready env env.func_type_indices.val.length) (hv.custom_ready env env.func_type_indices.val.length) bytes 0#usize env v4 tail v5 hparsed retained4
                      obtain ⟨⟨r, v6⟩, hready, retained6⟩ := WP.spec_imp_exists (hv.tail_ready env v5 tail retained5)
                      rw [hready]
                      cases r with
                      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                      | Ok u =>
                        cases u
                        simp
                        obtain ⟨⟨r, v7, remaining⟩, hdrain, retained7⟩ := WP.spec_imp_exists
                          (stream.retire_all_code_batches.spec_on visitor (ready env env.func_type_indices.val.length) moduleId v6 pending ((hv.batches env).poll env.func_type_indices.val.length) (retained6 rfl))
                        rw [hdrain]
                        simp only [bind_ok,uncurry_apply_pair,WP.spec_ok]
                        intro accepted
                        exact (retained7 accepted).2

/-- The streaming driver returns using a pre-environment invariant and a separate
ready-state invariant. Decoder acceptance establishes environment admissibility;
callbacks need not return on arbitrary fabricated scheduler records. -/
theorem stream.validate_streaming.spec_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V) (storage : metadata.Env)
    (hs : StreamSource.CallbacksTotal source state) (pre : V → Prop) (ready : metadata.Env → Nat → V → Prop) (admissible : metadata.Env → Prop)
    (hv : StreamScheduler.CallbacksOn visitor pre ready admissible ) (held : pre v)
    (decoded : ∀ bytes env next, bytes.length ≤ limits.MAX_MODULE_BYTES.val →
      metadata.validate_env bytes = .ok (.Ok (env,next)) → admissible env) :
    stream.validate_streaming source visitor moduleId state v storage ⦃ out =>
      out.1 = .Ok () → ready out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄ := by
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
      obtain ⟨v1, hregion, retained1⟩ := WP.spec_imp_exists (hv.region_pre v stream.Region.Environment held)
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
        have retained2 := metadata.validate_env_with.accepted_invariant _ pre hv.custom_pre bytes v1 env envEnd v2 hparsed retained1
        have admitted := decoded bytes env envEnd hsize herase
        have henv := (ModuleEnv.profile_accepted_entry_conditions bytes env envEnd hsize herase).1
        simp
        split
        · obtain ⟨⟨r, v3⟩, hr,retained3⟩ := WP.spec_imp_exists (stream.validate_remaining.spec_on source visitor moduleId state
            env envLen v2 hs pre ready admissible hv retained2 henv admitted)
          rw [hr]
          simpa only [bind_ok,uncurry_apply_pair,WP.spec_ok] using retained3
        · simp

end Itasca

end

/-! ## ReachedBatch -/

section

namespace Itasca
open Aeneas Aeneas.Std

/-- Batch index checks return before entry callbacks on an invalid index. -/
theorem stream.CodeBatch.validate_next.total_on {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V)
    (range : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (entry : metadata.validate_code_entry_with visitor batch.code batch.validated_end
      batch.env index v ⦃ _ => True ⦄) :
    stream.CodeBatch.validate_next visitor batch index v ⦃ _ => True ⦄ := by
  unfold stream.CodeBatch.validate_next
  split
  · simp
  · obtain ⟨expected,added,_⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := batch.first_func) (y := batch.num_validated) (by scalar_tac))
    rw [added]
    simp only [bind_ok]
    split
    · simp
    · exact entry

/-- Worker counter/error bookkeeping needs only the reached entry call to
return; no callbacks on other visitor states are assumed. -/
theorem stream.CodeBatch.validate_func.total_on {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V)
    (range : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (entry : metadata.validate_code_entry_with visitor batch.code batch.validated_end
      batch.env index v ⦃ _ => True ⦄) :
    stream.CodeBatch.validate_func visitor batch index v ⦃ _ => True ⦄ := by
  cases sticky : batch.error with
  | some error => rw [stream.CodeBatch.validate_func.sticky visitor batch index v error sticky]; simp
  | none =>
    obtain ⟨⟨result,after⟩,run,_⟩ := WP.spec_imp_exists
      (stream.CodeBatch.validate_next.total_on visitor batch index v range entry)
    cases result with
    | Err error => simp [stream.CodeBatch.validate_func,sticky,core.option.Option.is_none,run]
    | Ok finish =>
      have remaining := (stream.CodeBatch.validate_next.accepted visitor batch index finish v after run).1
      obtain ⟨count,added,_⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := batch.num_validated) (y := 1#usize) (by scalar_tac))
      simp [stream.CodeBatch.validate_func,sticky,core.option.Option.is_none,run,added]

/-- Complete worker validation reduces to actual decoded entry metadata and
its function-start/body calls, including all malformed-input rejection paths. -/
theorem stream.CodeBatch.validate_func.prepared_total {V : Type} (visitor : code.OpVisitor V)
    (batch : stream.CodeBatch) (index : Usize) (v : V)
    (bounds : CodeEntry.Bounds batch.env)
    (range : batch.first_func.val + batch.num_funcs.val ≤ batch.env.func_type_indices.val.length)
    (start : ∀ prepared : CodeEntry.Prepared batch.code batch.env index batch.validated_end,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish ⦃ _ => True ⦄)
    (bodyTotal : ∀ (prepared : CodeEntry.Prepared batch.code batch.env index batch.validated_end) started,
      visitor.on_function_start v prepared.ctx prepared.typeIdx prepared.bodyStart prepared.finish = .ok (.Ok (),started) →
      code.validate_body_with visitor prepared.body batch.env prepared.ctx prepared.typeIdx started ⦃ _ => True ⦄) :
    stream.CodeBatch.validate_func visitor batch index v ⦃ _ => True ⦄ := by
  exact stream.CodeBatch.validate_func.total_on visitor batch index v range
    (metadata.validate_code_entry_with.total_on visitor batch.code batch.validated_end batch.env index v
      bounds start bodyTotal)
end Itasca

end

/-! ## SchedulerComplete -/

section

/-!
# Accepting schedulers

Consequences of `StreamAcceptingScheduler.Accepts`, the scheduler policy under which completeness
holds, and of `StreamAcceptingScheduler.Valid`, the independent premises of an issued batch. Both
are defined in `Itasca/Contracts`. `StreamAcceptingScheduler.retire_complete` and
`StreamAcceptingScheduler.drain_complete` show that valid queued work retires and drains
successfully.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamAcceptingScheduler
/-- Running `validate_all` on the seed of a `Valid` batch gives a worker with the issued identity
that `stream.CodeBatch.finish` accepts. -/
theorem Valid.finished {issued : StreamBatch.Issued} (h : Valid issued)
    {after : stream.CodeBatch} (hr : stream.CodeBatch.validate_all issued.seed = .ok after) :
    StreamBatch.Identity issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) := by
  obtain ⟨entries, hn, ht, hb⟩ := h.entries
  obtain ⟨result, hrun, hreachable, hfinish⟩ := stream.CodeBatch.validate_all.complete_at_seed
    issued entries h.bounded hn ht h.limits h.entry_bounds hb
  have he : result = after := by simpa using hrun.symm.trans hr
  subst result
  exact ⟨hreachable.validation.1, hfinish⟩

end Itasca.StreamAcceptingScheduler

namespace Itasca

/-- A polled batch of the right module, whose ID is pending and whose finish check succeeds, is
retired successfully by `stream.retire_code_batch`. -/
theorem stream.retire_code_batch.complete {V : Type} (visitor : stream.StreamingVisitor V)
    (id : U64) (v v' : V) (pending : alloc.vec.Vec Usize) (batch : stream.CodeBatch)
    (hpoll : visitor.poll_code_batch v = .ok (.Ok batch, v'))
    (hmodule : batch.module_id = id) (hmem : batch.batch_id ∈ pending.val)
    (hfinish : stream.CodeBatch.finish batch = .ok (.Ok ())) :
    ∃ remaining, stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      (batch.batch_id :: remaining.val).Perm pending.val := by
  obtain ⟨found, hfind, hf⟩ := WP.spec_imp_exists
    (stream.retire_code_batch_loop.spec pending batch.batch_id 0#usize (by simp))
  have hlt : found.val < pending.length := by
    by_contra hnot
    have hend : found.val = pending.length := by have := hf.2.1; omega
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    exact hf.2.2.1 i hi (by simp) (by simpa [hend] using hi) he
  have hmatch := hf.2.2.2 hlt
  have hne : found ≠ alloc.vec.Vec.len pending := by scalar_tac
  have hs : stream.retire_code_batch visitor id v pending ⦃ r =>
      r.1 = .Ok () ∧ r.2.1 = v' ∧ (batch.batch_id :: r.2.2.val).Perm pending.val ⦄ := by
    simp [stream.retire_code_batch, hpoll, core.result.Result.Insts.CoreOpsTry.branch,
      hmodule, hfind, hne]
    step
    step
    step
    simp only [alloc.vec.Vec.pop, bind_ok, hfinish]
    refine ⟨rfl, rfl, ?_⟩
    have hlast : last.val = pending.val.length - 1 := by scalar_tac
    simpa only [index_mut_back_post, i3_post, hlast, alloc.vec.Vec.set_val_eq,
      alloc.vec.Vec.from_val, hmatch] using
      (StreamRetirement.swap_pop_perm pending.val found.val hlt)
  obtain ⟨⟨r, state, remaining⟩, hr, hsuccess, hstate, hperm⟩ := WP.spec_imp_exists hs
  dsimp only at hsuccess hstate hperm
  subst r
  subst state
  exact ⟨remaining, hr, hperm⟩

end Itasca

namespace Itasca.StreamAcceptingScheduler
/-- Valid pending work retires in any scheduler-selected order. Successful finish follows from the
actual worker execution on independently typed encodings. -/
theorem retire_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued) (id : U64)
    (queue : List StreamBatch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue)
    (hids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id))
    (hnonempty : pending.val ≠ []) :
    ∃ v' remaining rest,
      stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      Queued id rest v' ∧ ValidQueue id rest ∧
      remaining.val.Perm (rest.map StreamBatch.Issued.batch_id) ∧
      remaining.length + 1 = pending.length := by
  have hqueue : queue ≠ [] := by
    intro he
    have := hids.length_eq
    simp [he] at this
    exact hnonempty this
  obtain ⟨issued, rest, after, v', hperm, hpoll, hrun, hv'⟩ := hp.poll id queue v hv hvalid hqueue
  have hm : issued ∈ queue := hperm.mem_iff.mp (by simp)
  obtain ⟨hmodule, hissued⟩ := hvalid issued hm
  obtain ⟨hid, hfinish⟩ := hissued.finished hrun
  have hids' : (issued.batch_id :: rest.map StreamBatch.Issued.batch_id).Perm pending.val := by
    exact (hperm.map StreamBatch.Issued.batch_id).trans hids.symm
  obtain ⟨remaining, hr, hremoved⟩ := stream.retire_code_batch.complete visitor id v v'
    pending after hpoll (hid.1.trans hmodule)
    (by rw [hid.2.1]; exact hids'.mem_iff.mp (by simp)) hfinish
  refine ⟨v', remaining, rest, hr, hv', ?_, ?_, ?_⟩
  · intro entry he
    exact hvalid entry (hperm.mem_iff.mp (by simp [he]))
  · rw [hid.2.1] at hremoved
    exact List.Perm.cons_inv (hremoved.trans hids'.symm)
  · have := hremoved.length_eq
    simp only [List.length_cons] at this
    exact this

/-- Draining a valid queue terminates successfully and leaves no queued work. -/
theorem drain_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued) (id : U64)
    (queue : List StreamBatch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue)
    (hids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) :
    ∃ v' remaining,
      stream.retire_all_code_batches visitor id v pending = .ok (.Ok (), v', remaining) ∧
      remaining.val = [] ∧ Queued id [] v' := by
  generalize hn : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing queue v pending with
  | h n ih =>
    by_cases hempty : pending.val = []
    · have hqueue : queue = [] := by
        have hl := hids.length_eq
        simp [hempty] at hl
        exact hl
      refine ⟨v, pending, ?_, hempty, by simpa [hqueue] using hv⟩
      rw [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, loop]
      simp [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, hempty]
    · obtain ⟨v1, remaining, rest, hr, hv1, hrest, hids1, hlen⟩ :=
        retire_complete visitor config Queued hp id queue v pending hv hvalid hids hempty
      change remaining.val.length + 1 = pending.val.length at hlen
      obtain ⟨v', final, hrun, hnil, hv'⟩ := ih remaining.val.length (by omega)
        rest v1 remaining hv1 hrest hids1 rfl
      refine ⟨v', final, ?_, hnil, hv'⟩
      rw [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, loop]
      have hnon : pending.val.isEmpty = false := by simpa using hempty
      simpa [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, hnon, hr,
        core.result.Result.Insts.CoreOpsTry.branch, stream.retire_all_code_batches,
        stream.retire_all_code_batches_loop] using hrun

end Itasca.StreamAcceptingScheduler

end

/-! ## HeaderComplete -/

section

/-!
# Code section header completeness

`stream.read_code_header.complete`: an independently described code section header
(`StreamFraming.HeaderAt`) over an available source is accepted. Only the bounded header view of at
most 11 bytes is read.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A code region with a valid header (`StreamFraming.HeaderAt`) is accepted by
`stream.read_code_header` over an available source. Only a view of at most 11 bytes is read, and
nonminimal LEB128 prefixes are accepted. An absent region and a present zero-entry section are
separate cases. -/
theorem stream.read_code_header.complete {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : metadata.Env) (entries : Usize) (data : Slice U8)
    (environment tail : List U8)
    (havailable : StreamSource.Available source state environment data.val tail)
    (hsize : codeLen.val = data.length)
    (hbound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hheader : StreamFraming.HeaderAt data env entries) :
    stream.read_code_header source state codeLen env = .ok (.Ok entries) := by
  rcases hheader with ⟨hempty, rfl, hfuncs⟩ | ⟨count, hsection, hentries⟩
  · have hzero : codeLen = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa [Slice.length, hempty] using hsize
    simp [stream.read_code_header, hzero, alloc.vec.Vec.is_empty, hfuncs]
  · obtain ⟨content, hsection, hcount, hcountval⟩ := hsection
    obtain ⟨pos, size, hbyte, hsizeDecoded, hend, _⟩ := hsection
    change Leb128.Decoded data content count entries at hcount
    change count.val = env.func_type_indices.val.length at hcountval
    change data.length = content.val + size.val at hend
    have hpos : pos = 1#usize := by
      have hp := hbyte.byte.length
      apply UScalar.eq_of_val_eq
      simpa using hp
    subst pos
    have hsizeSpan : 1 < content.val ∧ content.val ≤ 6 ∧ content.val ≤ data.length := by
      simpa using hsizeDecoded.span
    have hcountSpan := hcount.span
    have hnonzero : codeLen ≠ 0#usize := by
      intro he
      have := hbyte.byte.bound
      scalar_tac
    let viewEnd := core.cmp.impls.OrdUsize.min codeLen 11#usize
    have hviewEnd : viewEnd.val = Nat.min data.length 11 := by
      simp [viewEnd, hsize]
    have hviewbound : viewEnd.val ≤ data.length := by rw [hviewEnd]; exact Nat.min_le_left _ _
    have hsizeWithin : content.val ≤ viewEnd.val := by rw [hviewEnd]; apply Nat.le_min.mpr; constructor <;> omega
    have hcountWithin : entries.val ≤ viewEnd.val := by rw [hviewEnd]; apply Nat.le_min.mpr; constructor <;> omega
    have hbyteWithin : (1#usize).val ≤ viewEnd.val := by scalar_tac
    obtain ⟨header, hread, hview⟩ := havailable.code_read 0#usize viewEnd (by simp) hviewbound
    have hlen : header.length = viewEnd.val - (0#usize).val := by
      change header.val.length = _
      rw [hview, List.slice_length]
      simpa using Nat.min_eq_right hviewbound
    have hexact := stream.read_exact.complete source state 0#usize viewEnd header
      (by simp) hread hlen
    have hsizeHeader : Leb128.Decoded header 1#usize size content :=
      hsizeDecoded.to_slice_view (by simp) hviewbound hview (by simp) (by simp) hsizeWithin
    have hcountHeader : Leb128.Decoded header content count entries :=
      hcount.to_slice_view (by simp) hviewbound hview (by simp) (by simp) hcountWithin
    have hbyteHeader := (Wasm1.BytesAt.of_slice_view (by simp) hviewbound hview).restrict
      hbyte.byte (pos := 0#usize) (next := 1#usize) (by simp) (by simp) hbyteWithin
    have hpositive : (0#usize).val < header.length := by have := hbyteHeader.bound; scalar_tac
    have hindex : Slice.index_usize header 0#usize = .ok 10#u8 := by
      have hs := hbyteHeader.suffix
      rw [List.drop_eq_getElem_cons hpositive] at hs
      have hhead := (List.cons.inj hs).1
      obtain ⟨id, hi, hival⟩ := WP.spec_imp_exists (Slice.index_usize_spec header 0#usize hpositive)
      have hid : id = 10#u8 := hival.trans hhead
      exact hid ▸ hi
    obtain ⟨len, hlenread, hlenval⟩ := stream.read_len.complete header 1#usize content size hsizeHeader
    obtain ⟨countLen, hcountread, hcountlen⟩ := stream.read_len.complete header content entries count hcountHeader
    have hcap : content.val + len.val ≤ limits.MAX_MODULE_BYTES.val := by
      omega
    obtain ⟨finish, hfinish, hfinishval⟩ := limits.add_offset.complete content len hcap
    have hfinishEq : finish = codeLen := by
      apply UScalar.eq_of_val_eq
      omega
    have hcountEq : countLen = alloc.vec.Vec.len env.func_type_indices := by
      apply UScalar.eq_of_val_eq
      exact hcountlen.trans hcountval
    have hnotOver : entries.val ≤ codeLen.val := by omega
    simp only [viewEnd] at hexact
    simp [stream.read_code_header, hnonzero, StreamFraming.header_limit, lift,
      hexact, core.result.Result.Insts.CoreOpsTry.branch, hindex, metadata.SECTION_CODE,
      hlenread, hfinish, hfinishEq, hcountread, hnotOver, hcountEq]

end Itasca

end

/-! ## DriverRegions -/

section

/-!
# Region certificates for streaming completeness

`StreamCompleteRegions.prepare` derives, from independent premises about a module (bounded
encoding, signature limits, elaboration, `Module_ok` typing and module restrictions), a
`StreamCompleteRegions.Certificate` for the canonical split of its bytes produced by
`stream.find_code_region`. The certificate gives the environment, code header and entries, tail,
and public metadata of the same raw module. It does not assume parser success or prevalidated
bodies. The file also transports independent encodings onto the split regions
(`ModuleBinary.At.on_region`).
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- An independent encoding of a complete region remains the same encoding
when that region is supplied as its own streaming buffer. -/
theorem At.on_region {α : Type} {R : α → List U8 → Prop}
    {data region : Slice U8} {start next : Usize} {value : α}
    (hregion : Wasm1.BytesAt data start region.val next)
    (h : At R data start value next) :
    At R region 0#usize value (Slice.len region) := by
  obtain ⟨bytes, he, hs⟩ := h
  refine ⟨bytes, he, hregion.restrict hs ?_ ?_ (Nat.le_refl _)⟩
  · simp
  · simpa using hregion.length

/-- Entries encoded within the implementation limits declare at most `limits.MAX_LOCALS` locals. -/
theorem Rep.locals_within_limits {entries bytes }
    (h : Rep (Itasca.Profile.CodeEncodingWithinLimits ) entries bytes) :
    ∀ entry ∈ entries, entry.declared.length ≤ limits.MAX_LOCALS.val := by
  induction h with
  | nil => simp
  | @cons entry entries first rest he hs ih =>
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact he.1
    · exact ih value hv

end Itasca.ModuleBinary

namespace Itasca.ModuleCode

/-- Generated typing of the code entries in index order and the local-count limit give the entry
certificates that streaming batches use. -/
theorem EntriesTyped.of_forall₂ {env entries i }
    (ht : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry ) (env.func_type_indices.val.drop i) entries)
    (hb : ∀ entry ∈ entries, entry.declared.length ≤ limits.MAX_LOCALS.val) :
    EntriesTyped env i entries := by
  induction entries generalizing i with
  | nil => exact .nil _
  | cons entry entries ih =>
    have hlen := ht.length_eq
    have hi : i < env.func_type_indices.val.length := by
      simp only [List.length_drop, List.length_cons] at hlen
      omega
    rw [List.drop_eq_getElem_cons hi] at ht
    cases ht with
    | cons he hs =>
      exact .cons ⟨hi, he, hb _ (by simp)⟩
        (ih hs (fun value hv => hb value (by simp [hv])))

end Itasca.ModuleCode

namespace Itasca.StreamCompleteRegions

open ModuleBinary ModuleElaboration

/-- Region certificates are derived from independent encoding and typing. They give the results
of the shared environment and tail validators and the encoded, typed code entries. Body checking
is later obtained from the typed, bounded encodings by the streaming driver. -/
structure Certificate (data : Slice U8) (raw : ModuleBinary.Module)
    (source : stream.SliceSource) (env : metadata.Env) (tail : metadata.Tail) : Prop where
  split : Split data source
  bytes : data.val = source.env.val ++ source.code.val ++ source.tail.val
  bounded : data.length ≤ limits.MAX_MODULE_BYTES.val
  environment : metadata.validate_env source.env = .ok (.Ok (env, Slice.len source.env))
  ready : ∃ decls, ModuleEnv.Ready raw 10 decls env
  entry_bounds : CodeEntry.Bounds env
  signature_limits : Itasca.Profile.EnvironmentWithinLimits env
  code : ∃ entries, StreamFraming.HeaderAt source.code env entries ∧
    At (Rep (Itasca.Profile.CodeEncodingWithinLimits )) source.code entries raw.codes (Slice.len source.code)
  typed : ModuleCode.EntriesTyped env 0 raw.codes
  code_count : raw.codes.length = env.func_type_indices.val.length
  tail_accepted : metadata.validate_tail source.tail 0#usize env = .ok (.Ok tail)
  realization : Matches env tail raw
  metadata : AccessorTypes env raw

private theorem slice_spec (data : Slice U8) (first last : Usize)
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨first, last⟩ ⦃ region => Wasm1.BytesAt data first region.val last ⦄ := by
  step
  apply Wasm1.BytesAt.of_slice_view hfirst hlast
  assumption

/-- Component completeness for the canonical streaming regions of an independently encoded,
elaborated, typed module. No assumption of parser or body success is made. -/
theorem prepare (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val )
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw ) :
    ∃ source env tail, Certificate data raw source env tail := by
  have hs := sections_of_typing he ht
  have hr := profile_requirements_of_typing he hs hp.toModuleConditions hsignatures
  obtain ⟨decls, codePos, tailPos, hl⟩ := ModuleLayout.normalize data raw hb
  have hsplit := stream.find_code_region.complete_layout hl
  obtain ⟨hcodePos, htailPos⟩ := stream.find_code_region.bounds data codePos tailPos hsplit
  obtain ⟨environment, henvSlice, henvSpan⟩ := WP.spec_imp_exists
    (slice_spec data 0#usize codePos (by simp) (by omega))
  obtain ⟨code, hcodeSlice, hcodeSpan⟩ := WP.spec_imp_exists
    (slice_spec data codePos tailPos hcodePos htailPos)
  obtain ⟨tailBytes, htailSlice, htailSpan⟩ := WP.spec_imp_exists
    (slice_spec data tailPos (Slice.len data) (by simpa using htailPos) (by simp))
  have henvEnc := hl.environment.on_region henvSpan
  obtain ⟨env, finalDecls, henv, hready⟩ := metadata.validate_env.profile_complete
    environment raw decls (Slice.len environment) henvEnc hl.raw_eq (.inl rfl) hr
  have henvSize : environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := henvSpan.length
    have := hb.1
    have := hl.environment.span.2
    simp only [Slice.length] at *
    omega
  obtain ⟨hbounds, hlimits⟩ := ModuleEnv.profile_accepted_entry_conditions
    environment env (Slice.len environment) henvSize henv
  have htailEnc := hl.tail.on_region htailSpan
  obtain ⟨segments, hsegments, hvalid⟩ := ModuleTail.materialize
    tailBytes 0#usize (Slice.len tailBytes) raw finalDecls env htailEnc hs hready
  let tail : metadata.Tail := ⟨segments⟩
  have hmatches := hready.matches tail hsegments
  have hsemantic := metadata.validate_env.profile_semantic_spec environment
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨_, hrep, hv, _, _, hprefix⟩ := hsemantic
  have hguards := hb.2.guards
  have hdeclared : ∀ entry ∈ raw.codes, DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body := by
    intro entry hm
    obtain ⟨j, hj, hjentry⟩ := List.mem_iff_getElem.mp hm
    have hidx : j < raw.functions.length := by rw [he.code_count]; exact hj
    have hfun : CodeEntry.function raw.functions[j] entry ∈
        List.zipWith CodeEntry.function raw.functions raw.codes := by
      apply List.mem_iff_getElem.mpr
      refine ⟨j, by simp only [List.length_zipWith]; omega, ?_⟩
      simp [List.getElem_zipWith, hjentry]
    have hd := hp.declared _ hfun
    apply hd.mono
    intro index hx
    apply (ModuleReferences.coherent_declared_iff (tables := raw.tables) (memories := raw.memories)
      (codes := raw.codes) hv.references hv.elements hvalid index).mpr
    rw [hmatches.1] at hx
    exact hx
  have hdataCount : ∀ count, env.data_count = some count → count.val = segments.val.length := by
    intro count hc
    have he : raw.dataCount = some count := (hready.dataCount_eq (by decide)).symm.trans hc
    have hv := hguards
    simpa [DataCountValid, he, ← hsegments] using hv
  have htail := metadata.validate_tail.complete tail (by simpa [tail, hsegments] using htailEnc) hvalid hdataCount
  have htypes := ModuleLayout.CodeAt.typed hready hs hguards hdeclared
  have hcount : raw.codes.length = env.func_type_indices.val.length := htypes.length_eq.symm
  have hcode : ∃ entries, StreamFraming.HeaderAt code env entries ∧
      At (Rep (Itasca.Profile.CodeEncodingWithinLimits )) code entries raw.codes (Slice.len code) := by
    rcases hl.code with hcode | ⟨hempty, hsame, _⟩
    · have henc := hcode.on_region hcodeSpan
      obtain ⟨content, hheader, hpayload⟩ := henc.section_split
      obtain ⟨count, entries, hn, hdecoded, hentries⟩ := hpayload.vector_split
      exact ⟨entries, .inr ⟨count, ⟨content, hheader, hdecoded, hn.trans hcount⟩,
        hentries.span.1.trans hentries.span.2⟩, hentries⟩
    · have hzero : code.val = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := hcodeSpan.length
        rw [hsame] at this
        omega
      have hfuncs : env.func_type_indices.val = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [hempty] using hcount.symm
      refine ⟨0#usize, .inl ⟨hzero, rfl, hfuncs⟩, [], ?_, ?_⟩
      · simpa [hempty] using (Rep.nil : Rep (Itasca.Profile.CodeEncodingWithinLimits ) [] [])
      · exact ⟨by simp [hzero], by simp [hzero], by simp⟩
  have htyped : ModuleCode.EntriesTyped env 0 raw.codes := by
    obtain ⟨_, _, bytes, henc, _⟩ := hcode
    apply ModuleCode.EntriesTyped.of_forall₂ (by simpa using htypes)
    exact henc.locals_within_limits
  obtain ⟨bytes, hprefix, _⟩ := hprefix
  have hnames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro entry hentry
    exact hprefix.export_names_wf (ModuleEnv.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have hmeta := accessorTypes hmatches.2 hv hnames (codes := raw.codes) (segments := tail.data.val)
  rw [← hmatches.1] at hmeta
  refine ⟨⟨environment, code, tailBytes⟩, env, tail, ?_⟩
  exact ⟨⟨codePos, tailPos, hsplit, henvSlice, hcodeSlice, htailSlice⟩,
    by simpa using ((henvSpan.append hcodeSpan).append htailSpan).suffix,
    hb.1, henv, ⟨finalDecls, hready⟩, hbounds, hlimits, hcode, htyped, hcount,
    htail, hmatches, hmeta⟩

end Itasca.StreamCompleteRegions

end
