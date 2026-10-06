import Itasca.ModuleReadyContexts
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

theorem raw_tables_projection (ts : List types.FuncType) (entries : List ModuleBinary.Import) :
    ModuleTranslation.tables (entries.map (fun e => importType ts e.desc)) =
      (ModuleSections.rawTables entries).map EnvTranslation.tableType := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [ModuleSections.rawTables, importType] at ih
    cases hd : e.desc <;> simp [ModuleTranslation.tables, importType, ModuleSections.rawTables, hd, ih]

theorem raw_memories_projection (ts : List types.FuncType) (entries : List ModuleBinary.Import) :
    ModuleTranslation.mems (entries.map (fun e => importType ts e.desc)) =
      (ModuleSections.rawMemories entries).map EnvTranslation.memType := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [ModuleSections.rawMemories, importType] at ih
    cases hd : e.desc <;> simp [ModuleTranslation.mems, importType, ModuleSections.rawMemories, hd, ih]

theorem limits_scalar {lim : types.Limits} {bound : U32}
    (h : ModuleTranslation.LimitsValid lim bound.val) : ModuleBinary.LimitsValid lim bound := by
  obtain ⟨hlo, hhi⟩ := h
  exact ⟨hlo, fun m hm => hhi m hm⟩

theorem external_index_valid {env : module.Env} {C : context} {desc : module.ExportDesc} {xt}
    (hc : CodeEntry.ModuleContext env C) (h : Externidx_ok C (exportIndex desc) xt) :
    ModuleSections.ExportDescValid env desc := by
  cases desc <;> cases h <;>
    simp_all [ModuleSections.ExportDescValid, hc.funcs, hc.globals, hc.tables, hc.mems, proj_uN_0]

/-- Generated typing and the independent Wasm 1.0 profile discharge every
semantic prerequisite of the environment parser at every declaration prefix. -/
theorem requirements_of_typing {raw : ModuleBinary.Module}
    (he : Elaborates raw (moduleOf raw)) (hs : SectionsTyped raw) (hp : Profile raw) :
    ModuleEnv.Requirements raw := by
  intro id decls env hlo hhi hr
  interval_cases id
  · exact hp.arity
  · constructor
    · intro entry hm
      have ht := hs.imports entry hm
      cases hd : entry.desc <;> simp only [hd, importType] at ht ⊢
      · exact (hr.types_eq (by decide)) ▸ he.imports entry hm _ hd
      · cases ht with
        | table _ ht _ =>
          exact limits_scalar (by simpa [limits.MAX_TABLE_ELEMS, U32.rMax] using table_valid_of_typing ht)
      · cases ht with
        | mem _ ht _ =>
          exact limits_scalar (by simpa [limits.MAX_MEMORY_PAGES] using memory_valid_of_typing ht)
    · have ht := hp.table_count
      simpa [hr.empty_tables (by decide), raw_tables_projection] using
        (show (ModuleTranslation.tables (raw.imports.map (fun e => importType raw.types e.desc))).length ≤ 1 by omega)
    · have hm := hp.memory_count
      simpa [hr.empty_memories (by decide), raw_memories_projection] using
        (show (ModuleTranslation.mems (raw.imports.map (fun e => importType raw.types e.desc))).length ≤ 1 by omega)
  · intro idx hi
    rw [hr.types_eq (by decide)]
    exact he.functions idx hi
  · constructor
    · intro tt ht
      exact limits_scalar (by simpa [limits.MAX_TABLE_ELEMS, U32.rMax] using table_valid_of_typing (hs.tables tt ht))
    · rw [hr.tables_count (by decide) (by decide)]
      exact hp.table_count
  · constructor
    · intro mt hm
      exact limits_scalar (by simpa [limits.MAX_MEMORY_PAGES] using memory_valid_of_typing (hs.memories mt hm))
    · rw [hr.memories_count (by decide) (by decide)]
      exact hp.memory_count
  · intro g hg
    exact global_valid_of_typing (hr.initializer_globals (by decide)) (hs.globals g hg)
  · constructor
    · have hn : ((raw.exports.map ModuleBinary.Export.name).map ModuleBinary.nameOfBytes).Nodup := by
        simpa [List.map_map, Function.comp_def] using hp.unique_exports
      exact List.Nodup.of_map ModuleBinary.nameOfBytes hn
    · intro e he
      obtain ⟨xt, ht⟩ := hs.exports e he
      have hx : Externidx_ok (contextOf raw) (exportIndex e.desc) xt := by cases ht; assumption
      exact external_index_valid (hr.moduleContext (by decide)) hx
  · intro idx hi
    exact start_valid_of_typing (hr.moduleContext (by decide)) (hs.start idx hi)
  · intro e hm
    obtain ⟨hexprs, hmode⟩ := element_parts (hs.elements e hm)
    obtain ⟨hidx, hconst⟩ := elemmode_active_properties hmode
    refine ⟨?_, ModuleConstants.valid_of_typing (hr.initializer_globals (by decide)) hconst, ?_⟩
    · simpa [initializerContextOf, hr.tables_context (by decide), proj_uN_0] using hidx
    · intro idx hi
      have ht : Expr_ok_const (initializerContextOf raw) [instr.REF_FUNC (.mk_uN idx.val)] .FUNCREF :=
        hexprs _ (List.mem_map.mpr ⟨idx, hi, rfl⟩)
      simpa [initializerContextOf, hr.funcs_context (by decide)] using ref_func_index ht

end Itasca.ModuleElaboration
