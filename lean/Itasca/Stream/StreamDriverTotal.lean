import Itasca.Stream.StreamSubmitTotal
import Itasca.Module.ModuleDecomposed
import Itasca.Module.ModuleCustomVisitor

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

theorem HeaderChecked.entries_le {S : Type} {source : stream.Source S} {state : S}
    {codeLen : Usize} {env : module.Env} {entries : Usize}
    (h : HeaderChecked source state codeLen env entries) : entries.val ≤ codeLen.val := by
  rcases h with ⟨rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hp, _⟩
  · simp
  · exact hp

end Itasca.StreamFraming

namespace Itasca

/-- After a decoded environment, all remaining phases return ordinarily under
returning source and visitor callbacks. Worker provenance is unnecessary. -/
theorem stream.validate_remaining.total_spec {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : module.Env) (envLen : Usize) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor)
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
                      (module.validate_tail_with.spec visitor.moduleModuleVisitorInst hv.custom
                        bytes 0#usize env v4 (by simp))
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

theorem stream.validate_remaining.total {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : module.Env) (envLen : Usize) (v : V)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor)
    (henv : CodeEntry.Bounds env) :
    ∃ r, stream.validate_remaining source visitor moduleId state env envLen v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.validate_remaining.total_spec source visitor moduleId state env envLen v hs hv henv)
  exact ⟨r, hr⟩

/-- Actual generic streaming validation returns ordinary success or error on
arbitrary bytes under returning callbacks. Successful batches are not assumed,
and neither source coherence nor scheduler provenance is a termination premise. -/
theorem stream.validate_streaming.wasm_total {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V) (storage : module.Env)
    (hs : StreamSource.CallbacksTotal source state) (hv : StreamScheduler.CallbacksTotal visitor) :
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
          (module.validate_env_with.spec visitor.moduleModuleVisitorInst hv.custom bytes v1)
        rw [hparsed]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨env, envEnd⟩ := pair
          have herase := module.validate_env_with.accepted_erase
            visitor.moduleModuleVisitorInst bytes v1 env envEnd v2 hparsed
          have henv := (ModuleEnv.accepted_entry_conditions bytes env envEnd hsize herase).1
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
