import Itasca.Module.Env.Preservation
import Itasca.Module.Env.Validity
import Itasca.Module.Env.Parser
import Itasca.Module.Env.Encoding

/-!
# Semantic contract of the environment parser

`module.validate_env.profile_semantic_spec` shows that for arbitrary bytes, `module.validate_env`
either rejects or returns an environment with `SemanticPostWith`. That is a `Represents`
declaration record, `Valid`, signature and size bounds, and an independent `PrefixEncoding` of the
consumed bytes. The same holds for `module.validate_env_with` with total custom-section hooks, and
the Wasm 1.0 instances are the `semantic_spec` theorems.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Validity follows a run of sections, alongside the raw declaration representation. -/
theorem Run.valid {profile} {data initial decls start initialId after afterDecls next id}
    (h : Run (profile := profile) data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hv : Valid initial profile) (hp : Phase initialId.val decls) :
    Valid after profile := by
  induction h with
  | nil => exact hv
  | custom _ _ ih => exact ih hv
  | step previous horder hh he ih =>
      exact he.valid (previous.represents hr hp) (ih hv) (previous.phase hp) horder

/-- An accepted environment comes with a declaration record that represents it, its semantic
checks, the signature and size bounds needed by the code and data parsers, and the independent byte
encoding of the consumed prefix. -/
def SemanticPostWith (profile : ValidationProfile) (data : Slice U8) : core.result.Result (module.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ decls, Represents env decls ∧ Valid env profile ∧
      SignatureBounded env next.val ∧ Bounded env next.val ∧
      ModuleBinary.At (fun ds bs => PrefixEncoding ds bs profile) data 0#usize decls next

/-- The run-based postcondition implies the semantic one. -/
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

/-- `SemanticPostWith` for Wasm 1.0. -/
abbrev SemanticPost (data : Slice U8) := SemanticPostWith .Wasm1 data

/-- `PostWith.semantic` for Wasm 1.0. -/
theorem Post.semantic {data result} (h : Post data result) : SemanticPost data result :=
  PostWith.semantic h

end Itasca.ModuleEnv

namespace Itasca

/-- Arbitrary bytes either make `module.validate_env` reject or yield an independently encoded,
semantically valid declaration prefix with consistent caches. -/
theorem module.validate_env.profile_semantic_spec (data : Slice U8) (profile : ValidationProfile) :
    module.validate_env data profile ⦃ ModuleEnv.SemanticPostWith profile data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.validate_env.profile_spec data profile)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

/-- Custom-section hooks may reject. Every successful result of `module.validate_env_with` still
satisfies the same binary and semantic contract. -/
theorem module.validate_env_with.profile_semantic_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (profile : ValidationProfile) (v : V) :
    module.validate_env_with visitor data profile v ⦃ r => ModuleEnv.SemanticPostWith profile data r.1 ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.validate_env_with.profile_spec visitor htotal data profile v)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

/-- `module.validate_env.profile_semantic_spec` for Wasm 1.0. -/
theorem module.validate_env.semantic_spec (data : Slice U8) :
    module.validate_env data .Wasm1 ⦃ ModuleEnv.SemanticPost data ⦄ := by
  exact module.validate_env.profile_semantic_spec data .Wasm1

/-- `module.validate_env_with.profile_semantic_spec` for Wasm 1.0. -/
theorem module.validate_env_with.semantic_spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (v : V) :
    module.validate_env_with visitor data .Wasm1 v ⦃ r => ModuleEnv.SemanticPost data r.1 ⦄ := by
  exact module.validate_env_with.profile_semantic_spec visitor htotal data .Wasm1 v

end Itasca
