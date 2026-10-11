import Itasca.Module.ModuleEnvPreservation
import Itasca.Module.ModuleEnvValidity
import Itasca.Module.ModuleEnvParser
import Itasca.Module.ModuleEnvEncoding

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Semantic validity follows the same ordered section history as the exact
raw declaration representation. -/
theorem Run.valid {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hv : Valid initial profile) (hp : Phase initialId.val decls) :
    Valid after profile := by
  induction h with
  | nil => exact hv
  | custom _ _ ih => exact ih hv
  | step previous horder hh he ih =>
      exact he.valid (previous.represents hr hp) (ih hv) (previous.phase hp) horder

/-- The same raw declaration witness carries exact bytes, all semantic checks,
and the cache/size invariants needed by the remaining code and data parsers. -/
def SemanticPostWith (profile : ValidationProfile) (data : Slice U8) : core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ decls, Represents env decls ∧ Valid env profile ∧
      SignatureBounded env next.val ∧ Bounded env next.val ∧
      ModuleBinary.At (fun ds bs => PrefixEncoding ds bs profile) data 0#usize decls next

theorem PostWith.semantic {profile data result} (h : PostWith profile data result) : SemanticPostWith profile data result := by
  cases result with
  | Err _ => trivial
  | Ok pair =>
      obtain ⟨env, next⟩ := pair
      obtain ⟨initial, start, decls, last, hinit, hheader, hrun, hbound⟩ := h
      have hi := module.Env.new.profile_declarations profile
      rw [hinit] at hi
      simp only [WP.spec_ok] at hi
      obtain ⟨hr, hv, hs, _, hp⟩ := hi
      exact ⟨decls, hrun.represents hr hp, hrun.valid hr hv hp,
        hrun.signatureBounded (hs.mono (Nat.zero_le _)), hbound, hrun.encoding hheader⟩

abbrev SemanticPost (data : Slice U8) := SemanticPostWith .Wasm1 data

theorem Post.semantic {data result} (h : Post data result) : SemanticPost data result :=
  PostWith.semantic h

end Itasca.ModuleEnv

namespace Itasca

/-- Arbitrary environment bytes either reject or produce the exact independently
encoded, semantically valid declaration prefix and consistent runtime caches. -/
theorem module.validate_env.profile_semantic_spec (data : Slice U8) (profile : ValidationProfile) :
    module.validate_env data profile ⦃ ModuleEnv.SemanticPostWith profile data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.validate_env.profile_spec data profile)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

/-- Custom-section callbacks may reject. Every successful returned environment
still satisfies the same independent binary and semantic contract. -/
theorem module.validate_env_with.profile_semantic_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (profile : ValidationProfile) (v : V) :
    module.validate_env_with visitor data profile v ⦃ r => ModuleEnv.SemanticPostWith profile data r.1 ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.validate_env_with.profile_spec visitor htotal data profile v)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

theorem module.validate_env.semantic_spec (data : Slice U8) :
    module.validate_env data .Wasm1 ⦃ ModuleEnv.SemanticPost data ⦄ := by
  exact module.validate_env.profile_semantic_spec data .Wasm1

theorem module.validate_env_with.semantic_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V) :
    module.validate_env_with visitor data .Wasm1 v ⦃ r => ModuleEnv.SemanticPost data r.1 ⦄ := by
  exact module.validate_env_with.profile_semantic_spec visitor htotal data .Wasm1 v

end Itasca
