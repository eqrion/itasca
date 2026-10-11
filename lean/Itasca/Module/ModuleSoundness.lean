import Itasca.Module.ModuleMetadata
import Itasca.Module.ModuleComposition
import Itasca.Profile.CodeEntry

open Aeneas Aeneas.Std

namespace Itasca.ModuleSound

open ModuleElaboration

/-- One independent decoded module accounts for every byte, the returned
declarations and data, generated SpecTec typing, the selected profile restrictions,
and the results of both public external-type accessors. -/
def Validated (data : Slice U8) (decoded : module.Module)
    (validationProfile : ValidationProfile := .Wasm1) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding validationProfile) raw data.val validationProfile ∧
    Elaborates raw (moduleOf raw) ∧ Matches decoded.env decoded.tail raw ∧
    Module_ok (moduleOf raw) ∧ Profile raw validationProfile ∧ AccessorTypes decoded.env raw

private theorem code_guards {env indices codes profile}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) indices codes) :
    (∀ entry ∈ codes, ∀ group ∈ entry.locals, ModuleBinary.ValueTypeAllowed profile group.2) ∧
    (env.data_count = none → ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false) := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    constructor
    · intro entry hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp.locals_allowed
      · exact ih.1 entry hm
    · intro hc entry hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp.no_data hc
      · exact ih.2 hc entry hm

private theorem assembly_guards {profile env decls codes} {segments : List module.Data}
    (hr : ModuleEnv.Represents env decls)
    (ha : ModuleBinary.ModuleTypesAllowed profile (decls.module [] []))
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val codes)
    (hs : ∀ segment ∈ segments, ModuleData.Valid env segment)
    (hc : ∀ count, env.data_count = some count → count.val = segments.length) :
    ModuleBinary.ModuleTypesAllowed profile (decls.module codes (segments.map ModuleData.raw)) ∧
    ModuleBinary.DataCountValid (decls.module codes (segments.map ModuleData.raw)) := by
  have hg := code_guards hcodes
  constructor
  · refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hg.1, ha.2.2.2.2.2.1, ?_⟩
    intro entry hm
    obtain ⟨actual, hactual, rfl⟩ := List.mem_map.mp hm
    have hv := hs actual hactual
    cases hm : actual.mode with
    | Passive => simp [ModuleData.raw, hm]
    | Active idx offset =>
      have ho : ModuleConstants.Valid env offset .I32 := by
        exact (show idx.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32 from by simpa [ModuleData.Valid, hm] using hv).2
      simpa only [ModuleData.raw, hm] using ho.const_allowed
        (show ModuleBinary.ValueTypeAllowed profile .I32 from by cases profile <;> trivial)
  · unfold ModuleBinary.DataCountValid
    change (match decls.dataCount with
      | none => ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false
      | some count => count.val = (segments.map ModuleData.raw).length)
    rw [hr.dataCount]
    cases he : env.data_count with
    | none => exact hg.2 he
    | some count => simpa using hc count he

/-- The three decoded byte regions and their semantic invariants suffice for
whole-module soundness. All witnesses concern the same AST and environment. -/
theorem assembled {validationProfile : ValidationProfile} {data : Slice U8} {env : module.Env} {tail : module.Tail}
    {decls : ModuleEnv.Declarations} {codes codePos tailPos}
    (henv : ModuleBinary.At (fun decls bytes => ModuleEnv.PrefixEncoding decls bytes validationProfile) data 0#usize decls codePos)
    (hrep : ModuleEnv.Represents env decls) (hv : ModuleEnv.Valid env validationProfile)
    (hcode : ModuleBinary.At
      (ModuleBinary.PaddedEncoding 10#u8 (ModuleBinary.VecEncoding (Itasca.Profile.CodeEncoding validationProfile)) [])
      data codePos codes tailPos)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry validationProfile) env.func_type_indices.val codes)
    (htail : ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes validationProfile) data tailPos
      (tail.data.val.map ModuleData.raw) (Slice.len data))
    (hsegments : ∀ segment ∈ tail.data.val, ModuleData.Valid env segment)
    (hdataCount : ∀ count, env.data_count = some count → count.val = tail.data.val.length) :
    Validated data ⟨env, tail⟩ validationProfile := by
  obtain ⟨preBytes, hp, hspan⟩ := henv
  have hiNames : ∀ entry ∈ env.imports.val,
      wf_name (ModuleBinary.nameOfBytes entry.module.val) ∧ wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro e he
    exact hp.import_names_wf (ModuleEnv.rawImport e) (by rw [hrep.imports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  have heNames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro e he
    exact hp.export_names_wf (ModuleEnv.rawExport e) (by rw [hrep.exports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  obtain ⟨xts, hxts⟩ := hv.exports_resolve
  refine ⟨fromEnv env decls.tables decls.memories codes tail.data.val, ?_,
    elaborates hrep.cache hcodes, matches_fromEnv tail hrep.cache,
    typed hrep.cache hv hiNames heNames hcodes hsegments hdataCount hxts,
    profile hrep.cache hv hcodes, accessorTypes hrep.cache hv heNames⟩
  rw [← represents_module hrep]
  have hg := assembly_guards hrep hp.allowed hcodes hsegments hdataCount
  exact ModuleComposition.whole_bytes ⟨preBytes, hp, hspan⟩ hcode htail hg.1 hg.2

/-- Composition of independently framed regions needs exact byte tiling, not a
shared allocation. Every semantic witness still belongs to one raw module. -/
theorem assembled_regions {validationProfile : ValidationProfile} {data : Slice U8} {env : module.Env} {tail : module.Tail}
    {decls : ModuleEnv.Declarations} {codes before codeBytes tailBytes}
    (hbytes : data.val = before ++ codeBytes ++ tailBytes)
    (henv : ModuleEnv.PrefixEncoding decls before validationProfile)
    (hrep : ModuleEnv.Represents env decls) (hv : ModuleEnv.Valid env validationProfile)
    (hcode : ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding (Itasca.Profile.CodeEncoding validationProfile)) [] codes codeBytes)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry validationProfile) env.func_type_indices.val codes)
    (htail : ModuleTail.Encoding (tail.data.val.map ModuleData.raw) tailBytes validationProfile)
    (hsegments : ∀ segment ∈ tail.data.val, ModuleData.Valid env segment)
    (hdataCount : ∀ count, env.data_count = some count → count.val = tail.data.val.length) :
    Validated data ⟨env, tail⟩ validationProfile := by
  have hiNames : ∀ entry ∈ env.imports.val,
      wf_name (ModuleBinary.nameOfBytes entry.module.val) ∧ wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro e he
    exact henv.import_names_wf (ModuleEnv.rawImport e)
      (by rw [hrep.imports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  have heNames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro e he
    exact henv.export_names_wf (ModuleEnv.rawExport e)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  obtain ⟨xts, hxts⟩ := hv.exports_resolve
  refine ⟨fromEnv env decls.tables decls.memories codes tail.data.val, ?_,
    elaborates hrep.cache hcodes, matches_fromEnv tail hrep.cache,
    typed hrep.cache hv hiNames heNames hcodes hsegments hdataCount hxts,
    profile hrep.cache hv hcodes, accessorTypes hrep.cache hv heNames⟩
  rw [hbytes, ← represents_module hrep]
  have hg := assembly_guards hrep henv.allowed hcodes hsegments hdataCount
  exact ModuleComposition.encoding henv hcode htail hg.1 hg.2

end Itasca.ModuleSound
