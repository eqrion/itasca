import Itasca.ModuleSoundness
import Itasca.ModuleEnvSemantics

open Aeneas Aeneas.Std

namespace Itasca

/-- The actual public validator returns on every input. Every accepted result
has exact binary provenance, generated module typing, the Wasm 1.0 profile,
and matching results from the actual public type accessors. -/
theorem module.validate_module.wasm_spec (data : Slice U8) :
    module.validate_module data ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded
      | .Err _ => True ⦄ := by
  unfold module.validate_module
  dsimp only
  split
  · simp
  · rename_i hsize
    have hsize' : data.length ≤ limits.MAX_MODULE_BYTES.val := by scalar_tac
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.validate_env.semantic_spec data)
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      rcases pair with ⟨env, codePos⟩
      obtain ⟨decls, hrep, hv, hsig, hbounded, henv⟩ := hp
      have hpos := henv.span.2
      have hbound : CodeEntry.Bounds env :=
        CodeEntry.Bounds.of_module_bound env (hsig.mono (by omega))
      obtain ⟨r, hcode, hp⟩ := WP.spec_imp_exists
        (module.validate_code.spec data codePos env hsize' hpos hbound hv.types)
      simp [core.result.Result.Insts.CoreOpsTry.branch, hcode]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok tailPos =>
        obtain ⟨codes, hcodes, htyped⟩ := (hp tailPos rfl).padded
        obtain ⟨r, htail, hp⟩ := WP.spec_imp_exists
          (module.validate_tail.spec data tailPos env hcodes.span.2)
        simp [htail]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok tail =>
          simp
          exact ModuleSound.assembled henv hrep hv hcodes htyped hp.1 hp.2

/-- No well-formed-input or environment hypothesis is needed for termination. -/
theorem module.validate_module.wasm_total (data : Slice U8) :
    ∃ r, module.validate_module data = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (module.validate_module.wasm_spec data)
  exact ⟨r, hr⟩

/-- Acceptance certifies one independently encoded, elaborated and typed
module, including the complete version profile and external-type metadata. -/
theorem module.validate_module.wasm_sound (data : Slice U8) (decoded : module.Module)
    (h : module.validate_module data = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded := by
  have hs := module.validate_module.wasm_spec data
  simpa [h] using hs

end Itasca
