import Itasca.Module.Env.Semantics
import Itasca.Profile.EntrySound
import Itasca.Profile.EntryPipeline

/-!
# Code entry validation under an accepted environment

Entry validation theorems whose environment premise is an accepted call of `metadata.validate_env`
on bounded input, instead of a hypothesis on the environment.
`ModuleEnv.profile_accepted_entry_conditions` extracts the allocation bounds and signature
admissibility from acceptance. The `_of_env` theorems then give totality, `Profile.Entry`
soundness and `CodeEntry.Validated` for `metadata.validate_code_entry` and
`metadata.validate_code_entry_with`. The code bytes may be in a different buffer from the
environment bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- An accepted environment decoded from input within the size limit supplies the entry
prerequisites for the profile: the allocation bound and signatures within the
completeness limits. -/
theorem profile_accepted_entry_conditions (data : Slice U8) (env : metadata.Env) (next : Usize)
     (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (h : metadata.validate_env data = .ok (.Ok (env, next))) :
    CodeEntry.Bounds env ∧ Profile.EnvironmentWithinLimits env := by
  have hs := metadata.validate_env.profile_semantic_spec data
  rw [h] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨decls, hr, hv, hsig, _, hb⟩ := hs
  exact ⟨CodeEntry.Bounds.of_module_bound env (hsig.mono (by have := hb.span.2; omega)),
    hv.environmentWithinLimits hr.cache⟩

end Itasca.ModuleEnv

namespace Itasca

end Itasca
