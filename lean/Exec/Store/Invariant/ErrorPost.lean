import Exec.Store.Preparation.AllocationErrors
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Attach a property of normal returns to a total extracted-call specification. -/
theorem normal_return_post {T : Type} {call : Result T} {post extra : T → Prop}
    (total : call ⦃ result => post result ⦄)
    (normal : ∀ result, call = .ok result → extra result) :
    call ⦃ result => post result ∧ extra result ⦄ := by
  obtain ⟨result, called, property⟩ := WP.spec_imp_exists total
  exact WP.exists_imp_spec ⟨result, called, property, normal result called⟩

end Exec.Store
