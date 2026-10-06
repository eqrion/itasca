import Itasca.ModuleEnvSlots
import Itasca.ModuleEnvDispatch
import Itasca.ModuleEnvPreservation
import Itasca.ModuleTypesSectionComplete
import Itasca.ModuleFunctionsComplete
import Itasca.ModuleTableSectionComplete
import Itasca.ModuleMemorySectionComplete
import Itasca.ModuleGlobalsComplete
import Itasca.ModuleImportsComplete
import Itasca.ModuleElementsComplete
import Itasca.ModuleExportsComplete

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections ModuleEnv

/-- Each ordered raw slot yields the actual dispatcher result and its exact
semantic update. No parser execution is assumed in the premises. -/
theorem module.decode_env_section.complete (data : Slice U8) (pos : Usize) (id : U8)
    (env : module.Env) (decls : Declarations) (raw : ModuleBinary.Module) (next : Usize)
    (hlo : 1 ≤ id.val) (hhi : id.val ≤ 9)
    (hb : At (Payload raw id.val) data pos () next)
    (hv : SectionValid raw id.val env) (hready : Ready raw (id.val - 1) decls env)
    (hbound : Bounded env pos.val) :
    ∃ result, module.decode_env_section data pos id env = .ok (.Ok next, result) ∧
      Effect data pos env decls id next result (update raw id.val decls) := by
  have hc : id.val = 1 ∨ id.val = 2 ∨ id.val = 3 ∨ id.val = 4 ∨ id.val = 5 ∨
      id.val = 6 ∨ id.val = 7 ∨ id.val = 8 ∨ id.val = 9 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h
  · have he : id = 1#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := module.decode_type_section.complete data pos env raw.types next hb hv hbound.types
    exact ⟨result, by simpa [module.decode_env_section, global_simps] using hr,
      .types ha hb hv⟩
  · have he : id = 2#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ImportEncoding) data pos raw.imports next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := module.decode_import_section.complete data pos env raw.imports next hb hv hbound
    refine ⟨result, by simpa [module.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw] using (Effect.imports (before := decls) ha (by simpa [Payload, update, hraw] using hb))
  · have he : id = 3#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, sigs, hr, ha⟩ := module.decode_function_section.complete data pos env raw.functions next hb hv hbound.funcs hbound.funcIndices
    exact ⟨result, by simpa [module.decode_env_section, global_simps] using hr,
      .functions ha hb⟩
  · have he : id = 4#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := module.decode_table_section.complete data pos env raw.tables next hb hv.1 hv.2
    refine ⟨result, by simpa [module.decode_env_section, global_simps] using hr, .tables ha hb ?_ ?_⟩
    · intro tt ht
      simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hv.1 tt ht
    · have hc : result.table_types.val.length ≤ 1 := by simpa only [ha.2, List.length_append] using hv.2
      exact hc.trans (Nat.le_max_right _ _)
  · have he : id = 5#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := module.decode_memory_section.complete data pos env raw.memories next hb hv.1 hv.2
    refine ⟨result, by simpa [module.decode_env_section, global_simps] using hr, .memories ha hb ?_ ?_⟩
    · intro mt ht
      simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid, Option.mem_def, global_simps] using hv.1 mt ht
    · have hc : result.mem_types.val.length ≤ 1 := by simpa only [ha.2, List.length_append] using hv.2
      exact hc.trans (Nat.le_max_right _ _)
  · have he : id = 6#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨result, hr, ha⟩ := module.decode_global_section.complete data pos env raw.globals next hb hv hbound.globals hbound.globalTypes
    refine ⟨result, by simpa [module.decode_env_section, global_simps] using hr, .globals ha hb ?_⟩
    intro g hg
    exact (hv g hg).append_globals _ ha.2.2 (by rw [ha.1])
  · have he : id = 7#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ExportEncoding) data pos raw.exports next at hb
    have hempty : env.exports.val = [] := by
      have hx := hready.represents.exports.symm.trans (hready.phase.2.2.2.2.2.2.1 (by decide))
      exact List.map_eq_nil_iff.mp hx
    obtain ⟨result, actual, hr, ha, hraw⟩ := module.decode_export_section.complete data pos env raw.exports next hb hempty hv.1 hv.2
    refine ⟨result, by simpa [module.decode_env_section, global_simps] using hr, ?_⟩
    simpa [Payload, update, hraw] using (Effect.exports (before := decls) ha (by simpa [Payload, update, hraw] using hb))
  · have he : id = 8#u8 := UScalar.eq_of_val_eq h
    subst id
    obtain ⟨bs, ⟨idx, hstart, hi⟩, hs⟩ := hb
    have hbytes : At StartEncoding data pos (some idx) next := ⟨bs, ⟨idx, rfl, hi⟩, hs⟩
    obtain ⟨hidx, hp, hr⟩ := hv idx hstart
    have hread := module.decode_start_section.complete data pos env idx next hbytes hidx hp hr
    refine ⟨{env with start := some idx}, by simpa [module.decode_env_section, global_simps] using hread, ?_⟩
    simpa [update, hstart] using (Effect.start (before := decls) rfl hbytes ⟨hidx, hp, hr⟩)
  · have he : id = 9#u8 := UScalar.eq_of_val_eq h
    subst id
    change At (VecEncoding ElementEncoding) data pos raw.elements next at hb
    obtain ⟨result, actual, hr, hraw, ha⟩ := module.decode_element_section.complete data pos env raw.elements next hb hv hbound.elements
    refine ⟨result, by simpa [module.decode_env_section, global_simps] using hr, ?_⟩
    have hva : ∀ e ∈ actual, ElementValid env e := by
      intro e he
      have hm : ModuleEnv.rawElement e ∈ raw.elements := by rw [← hraw]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      exact hv _ hm
    simpa [Payload, update, hraw] using (Effect.elements (before := decls) ha (by simpa [Payload, update, hraw] using hb) hva)

end Itasca
