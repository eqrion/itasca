import Itasca.Stream.DriverTotal
import Itasca.Module.Custom.Invariant
import Itasca.Stream.InvariantSubmission

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

/-- Reachable scheduler phases. Only custom-section hooks are globally total;
compilation callbacks are required on the states reached after environment setup. -/
structure CallbacksOn {V : Type} (visitor : stream.StreamingVisitor V)
    (pre : V → Prop) (ready : metadata.Env → Nat → V → Prop)
    (admissible : metadata.Env → Prop) (profile : ValidationProfile) : Prop where
  custom : ModuleTail.HooksTotal visitor.metadataModuleVisitorInst
  custom_pre : ModuleTail.PreservesInvariant visitor.metadataModuleVisitorInst pre
  custom_ready : ∀ env cursor, ModuleTail.PreservesInvariant visitor.metadataModuleVisitorInst (ready env cursor)
  region_pre : ∀ v region, pre v → visitor.custom_region v region ⦃ pre ⦄
  region_ready : ∀ env cursor v region, ready env cursor v → visitor.custom_region v region ⦃ ready env cursor ⦄
  environment : ∀ v env, pre v → admissible env → CodeEntry.Bounds env →
    visitor.environment_ready v env ⦃ out => ∀ config, out.1 = .Ok config → ready env 0 out.2 ⦄
  batches : ∀ env, StreamSubmission.CallbacksOn visitor env (ready env) profile
  code_end : ∀ env v, ready env env.func_type_indices.val.length v → visitor.code_end v ⦃ out => out.1 = .Ok () → ready env env.func_type_indices.val.length out.2 ⦄
  tail_ready : ∀ env v tail, ready env env.func_type_indices.val.length v →
    visitor.tail_ready v tail ⦃ out => out.1 = .Ok () → ready env env.func_type_indices.val.length out.2 ⦄

end Itasca.StreamScheduler

namespace Itasca

variable {profile : ValidationProfile}

/-- After a decoded environment, returning callbacks on reached states suffice.
No successful batch or worker-provenance premise is used. -/
theorem stream.validate_remaining.spec_on {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.Env) (envLen : Usize) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (pre : V → Prop) (ready : metadata.Env → Nat → V → Prop) (admissible : metadata.Env → Prop)
    (hv : StreamScheduler.CallbacksOn visitor pre ready admissible profile) (held : pre v)
    (henv : CodeEntry.Bounds env) (admitted : admissible env) :
    stream.validate_remaining source visitor moduleId profile state env envLen v ⦃ out => out.1 = .Ok () → ready env env.func_type_indices.val.length out.2 ⦄ := by
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
                        bytes 0#usize env v4 (by simp) (profile := profile))
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
    (hv : StreamScheduler.CallbacksOn visitor pre ready admissible profile) (held : pre v)
    (decoded : ∀ bytes env next, bytes.length ≤ limits.MAX_MODULE_BYTES.val →
      metadata.validate_env bytes profile = .ok (.Ok (env,next)) → admissible env) :
    stream.validate_streaming source visitor moduleId profile state v storage ⦃ out =>
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
        (metadata.validate_env_with.profile_spec visitor.metadataModuleVisitorInst hv.custom bytes profile v1)
      rw [hparsed]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨env, envEnd⟩ := pair
        have herase := metadata.validate_env_with.accepted_erase
          visitor.metadataModuleVisitorInst bytes v1 env envEnd v2 hparsed
        have retained2 := metadata.validate_env_with.accepted_invariant _ pre hv.custom_pre bytes v1 env envEnd v2 hparsed retained1
        have admitted := decoded bytes env envEnd hsize herase
        have henv := (ModuleEnv.profile_accepted_entry_conditions bytes env envEnd profile hsize herase).1
        simp
        split
        · obtain ⟨⟨r, v3⟩, hr,retained3⟩ := WP.spec_imp_exists (stream.validate_remaining.spec_on source visitor moduleId state
            env envLen v2 hs pre ready admissible hv retained2 henv admitted)
          rw [hr]
          simpa only [bind_ok,uncurry_apply_pair,WP.spec_ok] using retained3
        · simp

end Itasca
