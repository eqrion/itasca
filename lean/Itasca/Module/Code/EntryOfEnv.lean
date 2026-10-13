import Itasca.Module.Env.Semantics
import Itasca.Module.Code.EntryVisitor
import Itasca.Profile.EntrySound
import Itasca.Profile.EntryPipeline

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- An accepted bounded environment supplies the shared entry prerequisites,
including the selected profile's signature allocation bounds. -/
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

/-- A real bounded environment decode supplies the allocation and Wasm 1.0
arity prerequisites of separately invoked entry and code validators. The code
bytes may be in a different buffer. -/
theorem accepted_entry_conditions (data : Slice U8) (env : module.Env) (next : Usize)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (h : module.validate_env data .Wasm1 = .ok (.Ok (env, next))) :
    CodeEntry.Bounds env ∧ (∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) := by
  obtain ⟨hb, he, _⟩ := profile_accepted_entry_conditions data env next .Wasm1 hsize h
  exact ⟨hb, he.1⟩

end Itasca.ModuleEnv

namespace Itasca

/-- Visiting entry validation is total for either profile when the environment
was accepted from bounded input and every visitor hook terminates. -/
theorem module.validate_code_entry_with.profile_total_of_env {V : Type}
    (visitor : code.OpVisitor V) (htotal : FullVisitor.Total visitor)
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize)
    (v : V) (profile : ValidationProfile)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment profile = .ok (.Ok (env, next))) :
    ∃ r, module.validate_code_entry_with visitor data pos env index profile v = .ok r := by
  have hb := (ModuleEnv.profile_accepted_entry_conditions environment env next profile hsize henv).1
  exact module.validate_code_entry_with.profile_total visitor htotal data pos env index v hb profile

/-- Successful visiting entries carry the selected profile's independent
encoding and generated typing after an accepted environment decode. -/
theorem module.validate_code_entry_with.profile_sound_of_env {V : Type}
    (visitor : code.OpVisitor V) (environment data : Slice U8) (env : module.Env)
    (next pos index finish : Usize) (v v' : V) (profile : ValidationProfile)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment profile = .ok (.Ok (env, next)))
    (h : module.validate_code_entry_with visitor data pos env index profile v = .ok (.Ok finish, v')) :
    Profile.Entry profile data env index pos finish := by
  obtain ⟨hb, he, _⟩ := ModuleEnv.profile_accepted_entry_conditions environment env next profile hsize henv
  exact module.validate_code_entry_with.profile_sound visitor data pos env index finish v v' hb profile he.1 h

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

/-- Entry validation is total on arbitrary entry bytes and indices when its
environment came from an accepted bounded environment decode. On success the
exact entry bytes carry generated typing and the Wasm 1.0 body profile. -/
theorem module.validate_code_entry.spec_of_env
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment .Wasm1 = .ok (.Ok (env, next))) :
    module.validate_code_entry data pos env index .Wasm1 ⦃ r =>
      ∀ finish, r = .Ok finish → CodeEntry.Validated data env index pos finish ⦄ := by
  obtain ⟨hb, hr⟩ := ModuleEnv.accepted_entry_conditions environment env next hsize henv
  exact module.validate_code_entry.spec data pos env index hb hr

/-- An accepted compiler visitor certifies the same entry without a visitor
termination premise. Environment invariants come from the earlier actual call. -/
theorem module.validate_code_entry_with.wasm_sound_of_env {V : Type}
    (visitor : code.OpVisitor V) (environment data : Slice U8) (env : module.Env)
    (next pos index finish : Usize) (v v' : V)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment .Wasm1 = .ok (.Ok (env, next)))
    (h : module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok finish, v')) :
    CodeEntry.Validated data env index pos finish := by
  obtain ⟨hb, hr⟩ := ModuleEnv.accepted_entry_conditions environment env next hsize henv
  exact module.validate_code_entry_with.wasm_sound visitor data pos env index finish v v' hb hr h

/-- Hook termination suffices for totality of visiting entries; successful
validation is not a precondition. Rejection remains an ordinary error. -/
theorem module.validate_code_entry_with.total_of_env {V : Type}
    (visitor : code.OpVisitor V) (htotal : FullVisitor.Total visitor)
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize) (v : V)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment .Wasm1 = .ok (.Ok (env, next))) :
    ∃ r, module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok r := by
  have hb := (ModuleEnv.accepted_entry_conditions environment env next hsize henv).1
  exact module.validate_code_entry_with.total visitor htotal data pos env index v hb

end Itasca
