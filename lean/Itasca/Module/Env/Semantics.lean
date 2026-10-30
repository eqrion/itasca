import Itasca.Module.Env.Preservation
import Itasca.Module.Env.Validity
import Itasca.Module.Env.Parser
import Itasca.Module.Env.Encoding

/-!
# Semantic contract of the environment parser

`metadata.validate_env.profile_semantic_spec` shows that for arbitrary bytes, `metadata.validate_env`
either rejects or returns an environment with `SemanticPostWith`. That is a `Represents`
declaration record, `Valid`, signature and size bounds, and an independent `PrefixEncoding` of the
consumed bytes. The same holds for `metadata.validate_env_with` with total custom-section hooks, and
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
def SemanticPostWith (profile : ValidationProfile) (data : Slice U8) : core.result.Result (metadata.Env × Usize) error.Error → Prop
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
      have hi := metadata.Env.new.profile_declarations profile
      rw [hinit] at hi
      simp only [WP.spec_ok] at hi
      obtain ⟨hr, hv, hs, _, hp⟩ := hi
      exact ⟨decls, hrun.represents hr hp, hrun.valid hr hv hp,
        hrun.signatureBounded (hs.mono (Nat.zero_le _)), hbound, hrun.encoding hheader⟩

/-- `SemanticPostWith` for Wasm 1.0. -/
abbrev SemanticPost (data : Slice U8) := SemanticPostWith .Wasm1 data

end Itasca.ModuleEnv

namespace Itasca

/-- Arbitrary bytes either make `metadata.validate_env` reject or yield an independently encoded,
semantically valid declaration prefix with consistent caches. -/
theorem metadata.validate_env.profile_semantic_spec (data : Slice U8) (profile : ValidationProfile) :
    metadata.validate_env data profile ⦃ ModuleEnv.SemanticPostWith profile data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (metadata.validate_env.profile_spec data profile)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

/-- `metadata.validate_env.profile_semantic_spec` for Wasm 1.0. -/
theorem metadata.validate_env.semantic_spec (data : Slice U8) :
    metadata.validate_env data .Wasm1 ⦃ ModuleEnv.SemanticPost data ⦄ := by
  exact metadata.validate_env.profile_semantic_spec data .Wasm1

end Itasca
