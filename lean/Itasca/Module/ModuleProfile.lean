import Itasca.Module.ModuleDeclared
import Itasca.Body.Wasm1ProfileTransport
import Mathlib.Data.List.Nodup

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- Only labels matter to the Wasm 1.0 instruction profile. Its initial
function label is obtained from the raw module's own type declaration. -/
def profileContext (results : List types.ValueType) : context :=
  ⟨[], [], [], [], [], [], [], [], [.mk_list (results.map Translate.valueType)], none⟩

def FunctionProfile (types : List types.FuncType) (idx : U32) (entry : ModuleBinary.Code)
    (validationProfile : ValidationProfile := .Wasm1) : Prop :=
  ∃ hi : idx.val < types.length,
    Itasca.Profile.Instructions validationProfile (profileContext types[idx.val].results.val) entry.body

/-- The explicit version-specific conditions supplement the generated 2.0
judgment. Neither these conditions nor elaboration mention validator calls. -/
structure Profile (raw : ModuleBinary.Module) (validationProfile : ValidationProfile := .Wasm1) : Prop
    extends ModuleConditions raw validationProfile where
  bodies : List.Forall₂ (fun idx entry => FunctionProfile raw.types idx entry validationProfile) raw.functions raw.codes
  declared : DeclaredReferences.Module (moduleOf raw)

theorem typed_profile {env idx entry} {validationProfile : ValidationProfile}
    (h : CodeEntry.Typed env idx entry validationProfile) :
    FunctionProfile env.types.val idx entry validationProfile :=
  ⟨h.type_lt, h.profile.congr_labels _ rfl⟩

theorem code_profiles {env indices codes} {validationProfile : ValidationProfile}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry validationProfile) indices codes) :
    List.Forall₂ (fun idx entry => FunctionProfile env.types.val idx entry validationProfile) indices codes := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons (typed_profile hp) ih

theorem export_names_distinct {env : module.Env} {validationProfile : ValidationProfile} (hv : ModuleEnv.Valid env validationProfile) :
    (env.exports.val.map (fun e => ModuleBinary.nameOfBytes e.name.val)).Nodup := by
  have h := hv.distinctExports.map_on (f := ModuleBinary.nameOfBytes) ?_
  · simpa [List.map_map, Function.comp_def] using h
  · intro x hx y hy he
    obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ey, hey, rfl⟩ := List.mem_map.mp hy
    exact (hv.exportNames ex hex).nameOfBytes_injective (hv.exportNames ey hey) he

theorem profile {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) {validationProfile : ValidationProfile} (hv : ModuleEnv.Valid env validationProfile)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry validationProfile) env.func_type_indices.val codes) :
    Profile (fromEnv env tables memories codes segments) validationProfile := by
  constructor
  · constructor
    · simpa [fromEnv, ModuleEnv.rawExport, List.map_map, Function.comp_def] using export_names_distinct hv
    · have h := hv.tableCount
      rw [hc.tables, List.length_append] at h
      simpa [fromEnv, ModuleEnv.rawImport, List.map_map, Function.comp_def, tables_imports] using h
    · have h := hv.memoryCount
      rw [hc.memories, List.length_append] at h
      simpa [fromEnv, ModuleEnv.rawImport, List.map_map, Function.comp_def, mems_imports] using h
    · exact (hv.environment hc).1
  · exact code_profiles hcodes
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
