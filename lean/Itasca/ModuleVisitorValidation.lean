import Itasca.ModuleValidation
import Itasca.ModuleCodeTotal
import Itasca.ModuleCustomVisitor

open Aeneas Aeneas.Std

namespace Itasca

/-- The public visiting validator terminates when its callbacks terminate.
Entry overrides may defer validation entirely: this result makes no claim of
typing from their acceptance, and has no entry-validation premise. Bounds and
validity of the environment passed to hooks come from the actual first phase. -/
theorem module.validate_module_with.total_with_hooks {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V) (data : Slice U8) (v : V)
    (hm : ModuleTail.HooksTotal mv)
    (hc : ∀ env, CodeEntry.Bounds env → ModuleEnv.Valid env → ModuleCode.HooksTotal cv data env) :
    ∃ r, module.validate_module_with mv cv data v = .ok r := by
  have hs : module.validate_module_with mv cv data v ⦃ _ => True ⦄ := by
    unfold module.validate_module_with
    dsimp only
    split
    · simp
    · rename_i hsize
      have hsize' : data.length ≤ limits.MAX_MODULE_BYTES.val := by scalar_tac
      obtain ⟨⟨r, v1⟩, henv, hp⟩ := WP.spec_imp_exists
        (module.validate_env_with.semantic_spec mv hm data v)
      rw [henv]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        rcases pair with ⟨env, codePos⟩
        obtain ⟨decls, _, hv, hsig, _, hprefix⟩ := hp
        have hpos := hprefix.span.2
        have hb : CodeEntry.Bounds env := CodeEntry.Bounds.of_module_bound env
          (hsig.mono (by omega))
        obtain ⟨⟨r, v2⟩, hcode, hfinish⟩ := WP.spec_imp_exists
          (module.validate_code_with.total_spec cv data codePos env v1 (hc env hb hv) hsize' hpos)
        simp [core.result.Result.Insts.CoreOpsTry.branch, hcode]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok tailPos =>
          obtain ⟨⟨r, v3⟩, htail, _⟩ := WP.spec_imp_exists
            (module.validate_tail_with.spec mv hm data tailPos env v2 (hfinish tailPos rfl))
          simp [htail]
          cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists hs
  exact ⟨r, hr⟩

/-- A code-entry override that certifies every successful handoff yields the
same whole-module certificate as the default public validator. Totality and
entry correctness are explicit, separate callback obligations. -/
theorem module.validate_module_with.wasm_spec {V : Type}
    (mv : module.ModuleVisitor V) (cv : module.CodeVisitor V) (data : Slice U8) (v : V)
    (hm : ModuleTail.HooksTotal mv)
    (hc : ∀ env, CodeEntry.Bounds env → ModuleEnv.Valid env → ModuleCode.VisitorContract cv data env) :
    module.validate_module_with mv cv data v ⦃ r => match r.1 with
      | .Ok decoded => ModuleSound.Validated data decoded
      | .Err _ => True ⦄ := by
  unfold module.validate_module_with
  dsimp only
  split
  · simp
  · rename_i hsize
    have hsize' : data.length ≤ limits.MAX_MODULE_BYTES.val := by scalar_tac
    obtain ⟨⟨r, v1⟩, henv, hp⟩ := WP.spec_imp_exists
      (module.validate_env_with.semantic_spec mv hm data v)
    rw [henv]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      rcases pair with ⟨env, codePos⟩
      obtain ⟨decls, hrep, hv, hsig, _, hprefix⟩ := hp
      have hpos := hprefix.span.2
      have hb : CodeEntry.Bounds env := CodeEntry.Bounds.of_module_bound env
        (hsig.mono (by omega))
      obtain ⟨⟨r, v2⟩, hcode, hp⟩ := WP.spec_imp_exists
        (module.validate_code_with.spec cv data codePos env v1 (hc env hb hv) hsize' hpos)
      simp [core.result.Result.Insts.CoreOpsTry.branch, hcode]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok tailPos =>
        obtain ⟨codes, hcodes, htyped⟩ := (hp tailPos rfl).padded
        obtain ⟨⟨r, v3⟩, htail, hp⟩ := WP.spec_imp_exists
          (module.validate_tail_with.spec mv hm data tailPos env v2 hcodes.span.2)
        simp [htail]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok tail =>
          simp
          exact ModuleSound.assembled hprefix hrep hv hcodes htyped hp.1 hp.2

end Itasca
