import Itasca.Module.Env.Slots
import Itasca.Module.Env.Dispatch
import Itasca.Module.Env.Preservation
import Itasca.Module.Sections.TypeComplete
import Itasca.Module.Sections.FunctionComplete
import Itasca.Module.Sections.TableComplete
import Itasca.Module.Sections.MemoryComplete
import Itasca.Module.Sections.GlobalComplete
import Itasca.Module.Sections.ImportsComplete
import Itasca.Module.Sections.ElementComplete
import Itasca.Module.Sections.ExportComplete

/-!
# Section dispatch completeness

`metadata.decode_env_section.profile_complete` shows that `metadata.decode_env_section` accepts the
independent encoding of any declaration section whose contents are valid, and returns the
`Effect` that updates the declarations.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections ModuleEnv

/-- For an independently encoded section payload with valid contents, `metadata.decode_env_section`
returns success at the end of the payload together with the `Effect` of the matching slot update.
The premises do not assume any parser execution. -/
theorem metadata.decode_env_section.profile_complete (data : Slice U8) (pos : Usize) (id : U8)
    (env : metadata.Env) (decls : Declarations) (raw : ModuleBinary.Module) (next : Usize) (profile : ValidationProfile)
    (hlo : 1 ≤ (sectionRank id).val) (hhi : (sectionRank id).val ≤ 10)
    (hb : At (fun u bs => Payload raw (sectionRank id).val u bs profile) data pos () next)
    (hv : SectionValid raw (sectionRank id).val env profile) (hready : Ready raw ((sectionRank id).val - 1) decls env)
    (hbound : Bounded env pos.val) :
    ∃ result, metadata.decode_env_section data pos id env profile = .ok (.Ok next, result) ∧
      Effect (profile := profile) data pos env decls id next result (update raw (sectionRank id).val decls) := by
  have hc := sectionRank_prefix hlo hhi
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · have he : id = 1#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_type_section.profile_complete data pos env profile raw.types next hb
      (by intro ft hm; exact (Profile.funcTypeAdmissible_iff profile ft).mp (hv ft hm)) hbound.types
    exact ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr,
      .types ha hb hv⟩
  · have he : id = 2#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ImportEncoding) data pos raw.imports next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := metadata.decode_import_section.complete data pos env profile raw.imports next hb hv hbound
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.imports (profile := profile) (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb))
  · have he : id = 3#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, sigs, hr, ha⟩ := metadata.decode_function_section.complete data pos env raw.functions next hb hv hbound.funcs hbound.funcIndices
    exact ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr,
      .functions ha hb⟩
  · have he : id = 4#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_table_section.complete data pos env profile raw.tables next hb hv hbound.tables
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, .tables ha hb ?_⟩
    intro tt ht
    simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hv tt ht
  · have he : id = 5#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_memory_section.complete data pos env raw.memories next hb hv.1 hv.2
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, .memories ha hb ?_ ?_⟩
    · intro mt ht
      simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps] using hv.1 mt ht
    · have hc : result.mem_types.val.length ≤ 1 := by simpa only [ha.2, List.length_append] using hv.2
      exact hc.trans (Nat.le_max_right _ _)
  · have he : id = 6#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := metadata.decode_global_section.complete data pos env profile raw.globals next hb hv hbound.globals hbound.globalTypes hbound.declaredFuncs
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, .globals ha hb ?_⟩
    intro g hg
    exact (hv g hg).append_globals _ ha.2.2.1 (by rw [ha.1]) (by rw [ha.1])
  · have he : id = 7#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ExportEncoding) data pos raw.exports next at hb
    have hempty : env.exports.val = [] := by
      have hx := hready.represents.exports.symm.trans (hready.phase.2.2.2.2.2.2.1 (by decide))
      exact List.map_eq_nil_iff.mp hx
    obtain ⟨result, actual, hr, ha, hraw⟩ := metadata.decode_export_section.complete data pos env raw.exports next hb hempty hv.1 hv.2 hbound.declaredFuncs
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.exports (profile := profile) (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb))
  · have he : id = 8#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨bs, ⟨idx, hstart, hi⟩, hs⟩ := hb
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hi⟩, hs⟩
    obtain ⟨hidx, hp, hr⟩ := hv idx hstart
    have hread := metadata.decode_start_section.complete data pos env idx next hbytes hidx hp hr
    refine ⟨{env with start := some idx}, by simpa [metadata.decode_env_section, global_simps] using hread, ?_⟩
    simpa [update, hstart, sectionRank, global_simps] using (Effect.start (profile := profile) (before := decls) rfl hbytes ⟨hidx, hp, hr⟩)
  · have he : id = 9#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding (ElementEncodingFor profile)) data pos raw.elements next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := metadata.decode_element_section.profile_complete data pos env profile raw.elements next hb hv hbound.elements hbound.declaredFuncs
    refine ⟨result, by simpa [metadata.decode_env_section, global_simps] using hr, ?_⟩
    have hva : ∀ e ∈ actual, ElementValid env e := by
      intro e he
      have hm : ModuleEnv.rawElement e ∈ raw.elements := by rw [← hraw]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      exact hv _ hm
    simpa [Payload, update, hraw, sectionRank, global_simps] using (Effect.elements (profile := profile) (before := decls) ha (by simpa [Payload, update, hraw, sectionRank, global_simps] using hb) hva)
  · have he : id = 12#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (fun (_ : Unit) bs => StartEncoding raw.dataCount bs) data pos () next at hb
    obtain ⟨bs, hstart, hspan⟩ := hb
    obtain ⟨idx, hcount, hindex⟩ := hstart
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hindex⟩, hspan⟩
    have hread := metadata.decode_data_count.complete data pos env idx next hbytes
    refine ⟨{env with data_count := some idx}, by simpa [metadata.decode_env_section, global_simps] using hread, ?_⟩
    simpa [update, hcount, sectionRank] using (Effect.dataCount (before := decls) rfl hbytes)

end Itasca
