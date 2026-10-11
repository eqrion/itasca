import Itasca.Module.ModuleEnvSemantics
import Itasca.Module.ModuleEntryVisitor

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- A real bounded environment decode supplies the allocation and Wasm 1.0
arity prerequisites of separately invoked entry and code validators. The code
bytes may be in a different buffer. -/
theorem accepted_entry_conditions (data : Slice U8) (env : module.Env) (next : Usize)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (h : module.validate_env data = .ok (.Ok (env, next))) :
    CodeEntry.Bounds env ∧ (∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) := by
  have hs := module.validate_env.semantic_spec data
  rw [h] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨decls, _, hv, hsig, _, hb⟩ := hs
  exact ⟨CodeEntry.Bounds.of_module_bound env (hsig.mono (by have := hb.span.2; omega)), hv.types⟩

end Itasca.ModuleEnv

namespace Itasca

/-- Entry validation is total on arbitrary entry bytes and indices when its
environment came from an accepted bounded environment decode. On success the
exact entry bytes carry generated typing and the Wasm 1.0 body profile. -/
theorem module.validate_code_entry.spec_of_env
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment = .ok (.Ok (env, next))) :
    module.validate_code_entry data pos env index ⦃ r =>
      ∀ finish, r = .Ok finish → CodeEntry.Validated data env index pos finish ⦄ := by
  obtain ⟨hb, hr⟩ := ModuleEnv.accepted_entry_conditions environment env next hsize henv
  exact module.validate_code_entry.spec data pos env index hb hr

/-- An accepted compiler visitor certifies the same entry without a visitor
termination premise. Environment invariants come from the earlier actual call. -/
theorem module.validate_code_entry_with.wasm_sound_of_env {V : Type}
    (visitor : code.OpVisitor V) (environment data : Slice U8) (env : module.Env)
    (next pos index finish : Usize) (v v' : V)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment = .ok (.Ok (env, next)))
    (h : module.validate_code_entry_with visitor data pos env index v = .ok (.Ok finish, v')) :
    CodeEntry.Validated data env index pos finish := by
  obtain ⟨hb, hr⟩ := ModuleEnv.accepted_entry_conditions environment env next hsize henv
  exact module.validate_code_entry_with.wasm_sound visitor data pos env index finish v v' hb hr h

/-- Hook termination suffices for totality of visiting entries; successful
validation is not a precondition. Rejection remains an ordinary error. -/
theorem module.validate_code_entry_with.total_of_env {V : Type}
    (visitor : code.OpVisitor V) (htotal : FullVisitor.Total visitor)
    (environment data : Slice U8) (env : module.Env) (next pos index : Usize) (v : V)
    (hsize : environment.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment = .ok (.Ok (env, next))) :
    ∃ r, module.validate_code_entry_with visitor data pos env index v = .ok r := by
  have hb := (ModuleEnv.accepted_entry_conditions environment env next hsize henv).1
  exact module.validate_code_entry_with.total visitor htotal data pos env index v hb

end Itasca
