import Itasca.Profile.CodeEntry
import Itasca.Profile.BodyExecution
import Itasca.Module.Code.EntryWitness
import Itasca.Wasm2.Visitor.Total

/-!
# Profile code-entry pipeline

Totality of the extracted `module.validate_code_entry_with` for both profiles: `runBody.total` for
the body step, `profile_pipeline` for an execution witness (`CodeEntry.Witness`) on every
accepting run, and `profile_total` and `module.validate_code_entry.profile_total` for the
visitor and visitor-free entry validators.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Both body validators return a result, for a total visitor. -/
theorem CodeEntry.runBody.total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (profile : ValidationProfile)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (v : V) :
    ∃ r, CodeEntry.runBody visitor profile data env ctx index v = .ok r := by
  cases profile with
  | Wasm1 => exact code.validate_body_with.wasm_total visitor hv data env ctx v
  | Wasm2 => exact code.validate_multi_value_body_with.wasm_total visitor hv data env ctx index v

/-- Every accepting run of the entry validator, for either profile, has a `CodeEntry.Witness`
recording the type lookup, locals, body slice and visitor calls. -/
theorem module.validate_code_entry_with.profile_pipeline {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
    (profile : ValidationProfile) :
    module.validate_code_entry_with visitor data pos env index profile v ⦃ r =>
      ∀ finish, r.1 = .Ok finish →
        Nonempty (CodeEntry.Witness visitor data env index pos finish v r.2 profile) ⦄ :=
  module.validate_code_entry_with.pipeline_of_body_total visitor hv data pos env index v hbound profile
    (fun body ctx typeIdx started => CodeEntry.runBody.total visitor hv profile body env ctx typeIdx started)

/-- The entry validator with a total visitor returns a result. -/
theorem module.validate_code_entry_with.profile_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
    (profile : ValidationProfile) :
    ∃ r, module.validate_code_entry_with visitor data pos env index profile v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (module.validate_code_entry_with.profile_pipeline visitor hv data pos env index v hbound profile)
  exact ⟨r, hr⟩

/-- The visitor-free entry validator returns a result. -/
theorem module.validate_code_entry.profile_total (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (hbound : CodeEntry.Bounds env)
    (profile : ValidationProfile) :
    ∃ r, module.validate_code_entry data pos env index profile = .ok r := by
  obtain ⟨⟨r, v⟩, hr⟩ := module.validate_code_entry_with.profile_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data pos env index () hbound profile
  exact ⟨r, by simp [module.validate_code_entry, hr]⟩

end Itasca
