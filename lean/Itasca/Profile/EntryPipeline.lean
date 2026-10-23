import Itasca.Profile.CodeEntry
import Itasca.Module.Code.EntryWitness
import Itasca.Wasm2.Visitor.Total

/-!
# Profile code-entry pipeline

Totality of the extracted `module.validate_code_entry_with` for both profiles:
`profile_pipeline` gives an execution witness (`CodeEntry.Witness`) for every accepting run, and
`profile_total` and `module.validate_code_entry.profile_total` show that the visitor and
visitor-free entry validators return.
-/

open Aeneas Aeneas.Std

namespace Itasca

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
    (fun body ctx typeIdx started => code.validate_body_with.total visitor hv body env ctx typeIdx profile started)

/-- The entry validator with a total visitor returns a result. -/
theorem module.validate_code_entry_with.profile_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (v : V) (hbound : CodeEntry.Bounds env)
    (profile : ValidationProfile) :
    ∃ r, module.validate_code_entry_with visitor data pos env index profile v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (module.validate_code_entry_with.profile_pipeline visitor hv data pos env index v hbound profile)
  exact ⟨r, hr⟩

end Itasca
