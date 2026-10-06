import Itasca.ModuleValidation

open Aeneas Aeneas.Std

namespace Itasca.ModuleSound

open ModuleElaboration

/-- Composition of independently framed regions needs exact byte tiling, not a
shared allocation. Every semantic witness still belongs to one raw module. -/
theorem assembled_regions {data : Slice U8} {env : module.Env} {tail : module.Tail}
    {decls : ModuleEnv.Declarations} {codes before codeBytes tailBytes}
    (hbytes : data.val = before ++ codeBytes ++ tailBytes)
    (henv : ModuleEnv.PrefixEncoding decls before)
    (hrep : ModuleEnv.Represents env decls) (hv : ModuleEnv.Valid env)
    (hcode : ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding ModuleBinary.CodeEncoding) [] codes codeBytes)
    (hcodes : List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val codes)
    (htail : ModuleTail.Encoding (tail.data.val.map ModuleData.raw) tailBytes)
    (hsegments : ∀ segment ∈ tail.data.val, ModuleData.Valid env segment) :
    Validated data ⟨env, tail⟩ := by
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

namespace Itasca

/-- Successful default decomposed calls on adjacent spans inherit the entire
public module certificate, including binary provenance and external types. -/
theorem module.validate_module.wasm_sound_of_parts
    (data : Slice U8) (env : module.Env) (tail : module.Tail) (codePos tailPos : Usize)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env data = .ok (.Ok (env, codePos)))
    (hcode : module.validate_code data codePos env = .ok (.Ok tailPos))
    (htail : module.validate_tail data tailPos env = .ok (.Ok tail)) :
    ModuleSound.Validated data ⟨env, tail⟩ :=
  module.validate_module.wasm_sound data ⟨env, tail⟩
    (ModulePipeline.accepted_of_parts data env tail codePos tailPos hsize henv hcode htail)

/-- The environment, code, and tail may live in separate buffers. The first two
must be consumed exactly, and their concatenation must equal the claimed module
bytes. These are observable boundary checks, not parser or typing assumptions.
An empty code region is permitted when there are no defined functions. -/
theorem module.validate_module.regions_wasm_sound
    (data environment codeBytes tailBytes : Slice U8) (env : module.Env) (tail : module.Tail)
    (hbytes : data.val = environment.val ++ codeBytes.val ++ tailBytes.val)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : module.validate_env environment = .ok (.Ok (env, Slice.len environment)))
    (hcode : module.validate_code codeBytes 0#usize env = .ok (.Ok (Slice.len codeBytes)))
    (htail : module.validate_tail tailBytes 0#usize env = .ok (.Ok tail)) :
    ModuleSound.Validated data ⟨env, tail⟩ := by
  have heSize : environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hn := congrArg List.length hbytes
    simp only [List.length_append] at hn
    change data.val.length ≤ _ at hsize
    change environment.val.length ≤ _
    omega
  have hcSize : codeBytes.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hn := congrArg List.length hbytes
    simp only [List.length_append] at hn
    change data.val.length ≤ _ at hsize
    change codeBytes.val.length ≤ _
    omega
  have hs := module.validate_env.semantic_spec environment
  rw [henv] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨decls, hrep, hv, hsig, _, hprefix⟩ := hs
  have hbound : CodeEntry.Bounds env := CodeEntry.Bounds.of_module_bound env
    (hsig.mono (by simpa using heSize))
  have hc := module.validate_code.spec codeBytes 0#usize env hcSize (by simp) hbound hv.types
  rw [hcode] at hc
  simp only [WP.spec_ok] at hc
  obtain ⟨entries, hentries, htyped⟩ := (hc _ rfl).padded
  have ht := module.validate_tail.spec tailBytes 0#usize env (by simp)
  rw [htail] at ht
  simp only [WP.spec_ok] at ht
  obtain ⟨before, hp, hpSpan⟩ := hprefix
  obtain ⟨middle, hm, hmSpan⟩ := hentries
  obtain ⟨afterBytes, ha, haSpan⟩ := ht.1
  have hpEq : environment.val = before := by simpa using hpSpan.suffix
  have hmEq : codeBytes.val = middle := by simpa using hmSpan.suffix
  have haEq : tailBytes.val = afterBytes := by simpa using haSpan.suffix
  exact ModuleSound.assembled_regions (by simpa [hpEq, hmEq, haEq] using hbytes)
    hp hrep hv hm htyped ha ht.2

end Itasca
