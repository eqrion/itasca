import Itasca.ModuleEnvPreservation
import Itasca.ModuleEnvValidity
import Itasca.ModuleEnvParser
import Itasca.ModuleEnvEncoding

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Semantic validity follows the same ordered section history as the exact
raw declaration representation. -/
theorem Run.valid {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hv : Valid initial) (hp : Phase initialId.val decls) :
    Valid after := by
  induction h with
  | nil => exact hv
  | custom _ _ ih => exact ih
  | step previous horder hh he ih =>
      exact he.valid (previous.represents hr hp) ih (previous.phase hp) horder

/-- The same raw declaration witness carries exact bytes, all semantic checks,
and the cache/size invariants needed by the remaining code and data parsers. -/
def SemanticPost (data : Slice U8) : core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ decls, Represents env decls ∧ Valid env ∧
      SignatureBounded env next.val ∧ Bounded env next.val ∧
      ModuleBinary.At PrefixEncoding data 0#usize decls next

theorem Post.semantic {data result} (h : Post data result) : SemanticPost data result := by
  cases result with
  | Err _ => trivial
  | Ok pair =>
      obtain ⟨env, next⟩ := pair
      obtain ⟨initial, start, decls, last, hinit, hheader, hrun, hbound⟩ := h
      have hi := module.Env.new.declarations
      rw [hinit] at hi
      simp only [WP.spec_ok] at hi
      obtain ⟨hr, hv, hs, _, hp⟩ := hi
      exact ⟨decls, hrun.represents hr hp, hrun.valid hr hv hp,
        hrun.signatureBounded (hs.mono (Nat.zero_le _)), hbound, hrun.encoding hheader⟩

end Itasca.ModuleEnv

namespace Itasca

/-- Arbitrary environment bytes either reject or produce the exact independently
encoded, semantically valid declaration prefix and consistent runtime caches. -/
theorem module.validate_env.semantic_spec (data : Slice U8) :
    module.validate_env data ⦃ ModuleEnv.SemanticPost data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.validate_env.spec data)
  rw [hr]
  simpa only [WP.spec_ok] using hp.semantic

/-- Custom-section callbacks may reject. Every successful returned environment
still satisfies the same independent binary and semantic contract. -/
theorem module.validate_env_with.semantic_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V) :
    module.validate_env_with visitor data v ⦃ r => ModuleEnv.SemanticPost data r.1 ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.validate_env_with.spec visitor htotal data v)
  rw [hr]
  simpa only [WP.spec_ok] using hp.semantic

end Itasca
