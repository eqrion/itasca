import Itasca.Module.Elab.Declared
import Itasca.Support.ControlTranslation
import Mathlib.Data.List.Nodup

/-!
# Module-level profile

`Profile` collects the explicit conditions on a raw module under a `ValidationProfile` that the
generated 2.0 judgment does not express: `ModuleConditions` and declared function references. The theorem `profile`
derives it for a valid cached environment with typed code entries, and `elaborates` shows such a
module elaborates with in-bounds type references.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The explicit profile-specific conditions that supplement the generated 2.0 judgment. Neither
these conditions nor elaboration mention validator calls. -/
structure Profile (raw : ModuleBinary.Module) (validationProfile : ValidationProfile) : Prop
    extends ModuleConditions raw validationProfile where
  declared : DeclaredReferences.Module (moduleOf raw)

/-- Distinct export byte names in a valid environment have distinct decoded names. -/
theorem export_names_distinct {env : metadata.Env} {validationProfile : ValidationProfile} (hv : ModuleEnv.Valid env validationProfile) :
    (env.exports.val.map (fun e => ModuleBinary.nameOfBytes e.name.val)).Nodup := by
  have h := hv.distinctExports.map_on (f := ModuleBinary.nameOfBytes) ?_
  · simpa [List.map_map, Function.comp_def] using h
  · intro x hx y hy he
    obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ey, hey, rfl⟩ := List.mem_map.mp hy
    exact (hv.exportNames ex hex).nameOfBytes_injective (hv.exportNames ey hey) he

/-- A valid cached environment with typed code entries gives the module-level `Profile` of the
module it describes. -/
theorem profile {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) {validationProfile : ValidationProfile} (hv : ModuleEnv.Valid env validationProfile)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry validationProfile) env.func_type_indices.val codes) :
    Profile (fromEnv env tables memories codes segments) validationProfile := by
  constructor
  · constructor
    · simpa [fromEnv, ModuleEnv.rawExport, List.map_map, Function.comp_def] using export_names_distinct hv
    · have h := hv.memoryCount
      rw [hc.memories, List.length_append] at h
      simpa [fromEnv, ModuleEnv.rawImport, List.map_map, Function.comp_def, mems_imports] using h
  · change ∀ f ∈ List.zipWith CodeEntry.function env.func_type_indices.val codes,
      DeclaredReferences.Function _ f
    have hall : ∀ f ∈ List.zipWith CodeEntry.function env.func_type_indices.val codes,
        DeclaredReferences.Function
          (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) f := by
      generalize hi : env.func_type_indices.val = indices at hcodes ⊢
      clear hi
      induction hcodes with
      | nil => simp
      | cons hp htail ih =>
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hp.declared
        · exact ih f hf
    intro f hf
    exact (hall f hf).mono (ModuleReferences.coherent_declared hv.references)

/-- A cached environment with typed code entries elaborates its module with in-bounds type
references and matching code counts. -/
theorem elaborates {env tables memories codes segments} {validationProfile : ValidationProfile}
    (hc : ModuleEnv.Cache env tables memories)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry validationProfile) env.func_type_indices.val codes) :
    Elaborates (fromEnv env tables memories codes segments)
      (moduleOf (fromEnv env tables memories codes segments)) := by
  constructor
  · rfl
  · intro entry he idx hidx
    change entry ∈ env.imports.val.map ModuleEnv.rawImport at he
    obtain ⟨e, hmem, heq⟩ := (List.mem_map.mp he : ∃ e ∈ env.imports.val, ModuleEnv.rawImport e = entry)
    subst entry
    apply hc.import_indices idx
    simp only [ModuleEnv.importedFuncs, List.mem_filterMap]
    exact ⟨e, hmem, by simp [ModuleEnv.rawImport] at hidx; simp [hidx]⟩
  · intro idx hi
    change idx ∈ env.func_type_indices.val at hi
    change idx.val < env.types.val.length
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hi
    have hc' := hcodes.get hj (by rw [← hcodes.length_eq]; exact hj)
    simpa [List.get_eq_getElem, he] using hc'.type_lt
  · exact hcodes.length_eq

end Itasca.ModuleElaboration
