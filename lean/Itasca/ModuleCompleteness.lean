import Itasca.ModuleValidation
import Itasca.ModuleEnvComplete
import Itasca.ModuleRequirementsProof
import Itasca.ModuleReadyMetadata
import Itasca.ModuleCodeTypedComplete
import Itasca.ModuleDataMaterialize
import Itasca.ModuleTailComplete

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- Every independently encoded and elaborated Wasm 1.0 module satisfying the
implementation's byte/local limits and generated module typing is accepted by
the actual public validator. The returned declarations and data describe the
same input module; no parser-success or cache-coherence premise is required. -/
theorem module.validate_module.wasm_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw := by
  have hs := sections_of_typing he ht
  have hr := requirements_of_typing he hs hp
  obtain ⟨decls, codePos, tailPos, hl⟩ := ModuleLayout.normalize data raw hb
  obtain ⟨env, finalDecls, henv, hready⟩ := module.validate_env.complete
    data raw decls codePos hl.environment hl.raw_eq hl.stop hr
  have hsemantic := module.validate_env.semantic_spec data
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨_, _, _, hsig, _, _⟩ := hsemantic
  have hsize : data.length ≤ limits.MAX_MODULE_BYTES.val := hb.1
  have hbound : CodeEntry.Bounds env := CodeEntry.Bounds.of_module_bound env
    (hsig.mono (by have := hl.environment.span.2; omega))
  have hcode := hl.code.complete_of_sections hready hs hp hsize hbound
  obtain ⟨segments, hsegments, hv⟩ := ModuleTail.materialize
    data tailPos (Slice.len data) raw finalDecls env hl.tail hs hready
  let tail : module.Tail := ⟨segments⟩
  have htail := module.validate_tail.complete tail (by simpa [tail, hsegments] using hl.tail) hv
  exact ⟨⟨env, tail⟩, ModulePipeline.accepted_of_parts data env tail codePos tailPos
    hsize henv hcode htail, hready.matches tail hsegments⟩

/-- Completeness also exposes the successful public type accessors for that
same independently specified module, not merely for an existential witness. -/
theorem module.validate_module.wasm_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw := by
  obtain ⟨decoded, ha, hm⟩ := module.validate_module.wasm_complete data raw hb he ht hp
  obtain ⟨codePos, tailPos, henv, _, _⟩ := (ModulePipeline.accepted_parts data decoded ha).2
  have hsemantic := module.validate_env.semantic_spec data
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨decls, hrep, hv, _, _, hprefix⟩ := hsemantic
  obtain ⟨bytes, hprefix, _⟩ := hprefix
  have hn : ∀ entry ∈ decoded.env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro entry hentry
    exact hprefix.export_names_wf (ModuleEnv.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  refine ⟨decoded, ha, hm, ?_⟩
  have hmeta := accessorTypes hm.2 hv hn (codes := raw.codes) (segments := decoded.tail.data.val)
  rw [← hm.1] at hmeta
  exact hmeta

end Itasca
