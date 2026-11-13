import Itasca.Module.Elab.Metadata
import Itasca.Module.Composition
import Itasca.Profile.CodeEntry

/-!
# Assembling `ModuleSound.Validated`

Defines `Validated`, the soundness certificate of an accepted module, and assembles it from the
decoded regions. `assembled` takes the environment, code and tail spans of one input slice, and
`assembled_regions` takes byte lists that tile the input. Both use the byte composition from
`Module/Composition` and the elaboration and typing results from `Module/Elab`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSound

open ModuleElaboration

/-- A raw module from the independent grammar that encodes exactly `data` under the profile's
code encoding, elaborates to `moduleOf raw`, matches the returned environment and tail, satisfies
the generated `Module_ok`, meets the profile restrictions, and has the types returned by the
public external-type accessors. -/
def Validated (data : Slice U8) (decoded : metadata.Module)
    (validationProfile : ValidationProfile) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding validationProfile) raw data.val validationProfile ∧
    Elaborates raw (moduleOf raw) ∧ Matches decoded.env decoded.tail raw ∧
    Module_ok (moduleOf raw) ∧ Profile raw validationProfile ∧ AccessorTypes decoded.env raw

private theorem code_guards {env indices codes profile}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) indices codes) :
    env.data_count = none → ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    intro hc entry hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hp.no_data hc
    · exact ih hc entry hm

private theorem assembly_guards {profile env decls codes} {segments : List metadata.Data}
    (hr : ModuleEnv.Represents env decls)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val codes)
    (hc : ∀ count, env.data_count = some count → count.val = segments.length) :
    ModuleBinary.DataCountValid (decls.module codes (segments.map ModuleData.raw)) := by
  unfold ModuleBinary.DataCountValid
  change (match decls.dataCount with
    | none => ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false
    | some count => count.val = (segments.map ModuleData.raw).length)
  rw [hr.dataCount]
  cases he : env.data_count with
  | none => exact code_guards hcodes he
  | some count => simpa using hc count he

/-- Like `assembled`, from byte lists that tile `data` exactly as `before ++ codeBytes ++
tailBytes` instead of spans of one slice. Every semantic witness still belongs to one raw
module. -/
theorem assembled_regions {validationProfile : ValidationProfile} {data : Slice U8} {env : metadata.Env} {tail : metadata.Tail}
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
  have hg := assembly_guards hrep hcodes hdataCount
  exact ModuleComposition.encoding henv hcode htail hg

end Itasca.ModuleSound
