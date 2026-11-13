import Itasca.Module.Env.Preservation
import Itasca.Module.Env.Validity
import Itasca.Module.Env.Parser
import Itasca.Module.Env.Encoding

/-!
# Semantic contract of the environment parser

`metadata.validate_env.profile_semantic_spec` shows that for arbitrary bytes, `metadata.validate_env`
either rejects or returns an environment with `SemanticPostWith`. That is a `Represents`
declaration record, `Valid`, signature and size bounds, and an independent `PrefixEncoding` of the
consumed bytes. The same holds for `metadata.validate_env_with` with total custom-section hooks.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Validity follows a run of sections, alongside the raw declaration representation. -/
theorem Run.valid {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hv : Valid initial) (hp : Phase initialId.val decls) :
    Valid after := by
  induction h with
  | nil => exact hv
  | custom _ _ ih => exact ih
  | step previous horder hh he ih =>
      exact he.valid (previous.represents hr hp) ih (previous.phase hp) horder

/-- An accepted environment comes with a declaration record that represents it, its semantic
checks, the signature and size bounds needed by the code and data parsers, and the independent byte
encoding of the consumed prefix. -/
def SemanticPostWith (data : Slice U8) : core.result.Result (metadata.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ decls, Represents env decls ∧ Valid env ∧
      SignatureBounded env next.val ∧ Bounded env next.val ∧
      ModuleBinary.At (fun ds bs => PrefixEncoding ds bs) data 0#usize decls next

/-- The run-based postcondition implies the semantic one. -/
theorem PostWith.semantic {data result} (h : PostWith data result) : SemanticPostWith data result := by
  cases result with
  | Err _ => trivial
  | Ok pair =>
      obtain ⟨env, next⟩ := pair
      obtain ⟨initial, start, decls, last, hinit, hheader, hrun, hbound⟩ := h
      have hi := metadata.Env.new.profile_declarations
      rw [hinit] at hi
      simp only [WP.spec_ok] at hi
      obtain ⟨hr, hv, hs, _, hp⟩ := hi
      exact ⟨decls, hrun.represents hr hp, hrun.valid hr hv hp,
        hrun.signatureBounded (hs.mono (Nat.zero_le _)), hbound, hrun.encoding hheader⟩

end Itasca.ModuleEnv

namespace Itasca

/-- Arbitrary bytes either make `metadata.validate_env` reject or yield an independently encoded,
semantically valid declaration prefix with consistent caches. -/
theorem metadata.validate_env.profile_semantic_spec (data : Slice U8) :
    metadata.validate_env data ⦃ ModuleEnv.SemanticPostWith data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (metadata.validate_env.profile_spec data)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

end Itasca
