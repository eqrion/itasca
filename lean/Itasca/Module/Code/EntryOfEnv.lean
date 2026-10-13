import Itasca.Module.Env.Semantics
import Itasca.Module.Code.EntryVisitor
import Itasca.Profile.EntrySound
import Itasca.Profile.EntryPipeline

/-!
# Code entry validation under an accepted environment

Entry validation theorems whose environment premise is an accepted call of `module.validate_env`
on bounded input, instead of a hypothesis on the environment.
`ModuleEnv.profile_accepted_entry_conditions` extracts the allocation bounds and signature
admissibility from acceptance. The `_of_env` theorems then give totality, `Profile.Entry`
soundness and `CodeEntry.Validated` for `module.validate_code_entry` and
`module.validate_code_entry_with`. The code bytes may be in a different buffer from the
environment bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- An accepted environment decoded from input within the size limit supplies the entry
prerequisites for the profile: the allocation bound, admitted signatures, and signatures within the
completeness limits. -/
theorem profile_accepted_entry_conditions (data : Slice U8) (env : module.Env) (next : Usize)
    (profile : ValidationProfile) (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (h : module.validate_env data profile = .ok (.Ok (env, next))) :
    CodeEntry.Bounds env ∧ Profile.Environment profile env ∧
      Profile.EnvironmentWithinLimits profile env := by
  have hs := module.validate_env.profile_semantic_spec data profile
  rw [h] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨decls, hr, hv, hsig, _, hb⟩ := hs
  exact ⟨CodeEntry.Bounds.of_module_bound env (hsig.mono (by have := hb.span.2; omega)),
    hv.environment hr.cache, hv.environmentWithinLimits hr.cache⟩

/-- A Wasm 1.0 environment accepted from bounded input supplies the allocation bound and the
single-result arity needed by separately invoked entry validators. The code bytes may be in a
different buffer. -/
theorem accepted_entry_conditions (data : Slice U8) (env : module.Env) (next : Usize)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (h : module.validate_env data .Wasm1 = .ok (.Ok (env, next))) :
    CodeEntry.Bounds env ∧ (∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) := by
  obtain ⟨hb, he, _⟩ := profile_accepted_entry_conditions data env next .Wasm1 hsize h
  exact ⟨hb, he.1⟩

end Itasca.ModuleEnv

namespace Itasca

/-- `module.validate_code_entry_with` is total for either profile when the environment was accepted
from bounded input and every visitor hook terminates. -/
theorem module.validate_code_entry_with.profile_total_of_env {V : Type}
    (visitor : code.OpVisitor V) (htotal : FullVisitor.Total visitor)
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize)
    (v : V) (profile : ValidationProfile)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment profile = .ok (.Ok (env, next))) :
    ∃ r, module.validate_code_entry_with visitor data pos env index profile v = .ok r := by
  have hb := (ModuleEnv.profile_accepted_entry_conditions environment env next profile hsize henv).1
  exact module.validate_code_entry_with.profile_total visitor htotal data pos env index v hb profile

/-- A successful `module.validate_code_entry_with` call under an accepted environment gives
`Profile.Entry`: the independent encoding and generated typing for the selected profile. -/
theorem module.validate_code_entry_with.profile_sound_of_env {V : Type}
    (visitor : code.OpVisitor V) (environment data : Slice U8) (env : module.Env)
    (next pos index finish : Usize) (v v' : V) (profile : ValidationProfile)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment profile = .ok (.Ok (env, next)))
    (h : module.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok finish, v')) :
    Profile.Entry profile data env index pos finish := by
  obtain ⟨hb, he, _⟩ := ModuleEnv.profile_accepted_entry_conditions environment env next profile hsize henv
  exact module.validate_code_entry_with.profile_sound visitor data pos env index finish v v' hb profile he.1 h

/-- `module.validate_code_entry` under an accepted environment terminates for either profile, and
success gives `Profile.Entry`. -/
theorem module.validate_code_entry.profile_spec_of_env
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize)
    (profile : ValidationProfile)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment profile = .ok (.Ok (env, next))) :
    module.validate_code_entry data pos env index profile ⦃ r =>
      ∀ finish, r = .Ok finish → Profile.Entry profile data env index pos finish ⦄ := by
  obtain ⟨hb, he, _⟩ := ModuleEnv.profile_accepted_entry_conditions environment env next profile hsize henv
  obtain ⟨⟨r, u⟩, hr⟩ := module.validate_code_entry_with.profile_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data pos env index () hb profile
  cases u
  have hrun : module.validate_code_entry data pos env index profile = .ok r := by
    simp [module.validate_code_entry, hr]
  rw [hrun]
  simp only [WP.spec_ok]
  intro finish hf
  subst r
  exact module.validate_code_entry_with.profile_sound code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    data pos env index finish () () hb profile he.1 hr

/-- `module.validate_code_entry` terminates on arbitrary entry bytes and indices when its
environment was accepted from bounded input. On success the entry bytes carry generated typing and
the Wasm 1.0 body profile. -/
theorem module.validate_code_entry.spec_of_env
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment .Wasm1 = .ok (.Ok (env, next))) :
    module.validate_code_entry data pos env index .Wasm1 ⦃ r =>
      ∀ finish, r = .Ok finish → CodeEntry.Validated data env index pos finish ⦄ := by
  obtain ⟨hb, hr⟩ := ModuleEnv.accepted_entry_conditions environment env next hsize henv
  exact module.validate_code_entry.spec data pos env index hb hr

/-- A successful `module.validate_code_entry_with` call for any visitor gives `Validated`, with no
visitor termination premise. The environment invariants come from the accepted `module.validate_env`
call. -/
theorem module.validate_code_entry_with.wasm_sound_of_env {V : Type}
    (visitor : code.OpVisitor V) (environment data : Slice U8) (env : module.Env)
    (next pos index finish : Usize) (v v' : V)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment .Wasm1 = .ok (.Ok (env, next)))
    (h : module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) :
    CodeEntry.Validated data env index pos finish := by
  obtain ⟨hb, hr⟩ := ModuleEnv.accepted_entry_conditions environment env next hsize henv
  exact module.validate_code_entry_with.wasm_sound visitor data pos env index finish v v' hb hr h

/-- Hook termination suffices for `module.validate_code_entry_with` to terminate, and successful
validation is not a precondition. Rejection is an ordinary error. -/
theorem module.validate_code_entry_with.total_of_env {V : Type}
    (visitor : code.OpVisitor V) (htotal : FullVisitor.Total visitor)
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize) (v : V)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment .Wasm1 = .ok (.Ok (env, next))) :
    ∃ r, module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok r := by
  have hb := (ModuleEnv.accepted_entry_conditions environment env next hsize henv).1
  exact module.validate_code_entry_with.total visitor htotal data pos env index v hb

end Itasca
