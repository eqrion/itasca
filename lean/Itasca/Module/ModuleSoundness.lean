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
    (hsegments : ∀ segment ∈ tail.data.val, ModuleData.Valid env segment) :
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
    typed hrep.cache hv hiNames heNames hcodes hsegments hxts,
    profile hrep.cache hv hcodes, accessorTypes hrep.cache hv heNames⟩
  rw [← represents_module hrep]
  exact ModuleComposition.whole_bytes ⟨preBytes, hp, hspan⟩ hcode htail

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
    (hsegments : ∀ segment ∈ tail.data.val, ModuleData.Valid env segment) :
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
    typed hrep.cache hv hiNames heNames hcodes hsegments hxts,
    profile hrep.cache hv hcodes, accessorTypes hrep.cache hv heNames⟩
  rw [hbytes, ← represents_module hrep]
  exact ModuleComposition.encoding henv hcode htail

end Itasca.ModuleSound
