import Itasca.Module.Env.ReadyContexts
import Mathlib.Tactic.IntervalCases

/-!
# Requirements from typing

`profile_requirements_of_typing` derives `ModuleEnv.Requirements`, the semantic requirements of
every declaration section, from the generated typing of the sections, the module-level profile
conditions and the signature limits. `requirements_of_typing` is the Wasm 1.0 form.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The table space translated from raw import types is the translation of `rawTables`. -/
theorem raw_tables_projection (ts : List wasm_types.FuncType) (entries : List ModuleBinary.Import) :
    ModuleTranslation.tables (entries.map (fun e => importType ts e.desc)) =
      (ModuleSections.rawTables entries).map EnvTranslation.tableType := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [ModuleSections.rawTables, importType] at ih
    cases hd : e.desc <;> simp [ModuleTranslation.tables, importType, ModuleSections.rawTables, hd, ih]

/-- The memory space translated from raw import types is the translation of `rawMemories`. -/
theorem raw_memories_projection (ts : List wasm_types.FuncType) (entries : List ModuleBinary.Import) :
    ModuleTranslation.mems (entries.map (fun e => importType ts e.desc)) =
      (ModuleSections.rawMemories entries).map EnvTranslation.memType := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [ModuleSections.rawMemories, importType] at ih
    cases hd : e.desc <;> simp [ModuleTranslation.mems, importType, ModuleSections.rawMemories, hd, ih]

/-- Limits valid in the SpecTec sense are valid in the binary sense for the same bound. -/
theorem limits_scalar {lim : wasm_types.Limits} {bound : U32}
    (h : ModuleTranslation.LimitsValid lim bound.val) : ModuleBinary.LimitsValid lim bound := by
  obtain ⟨hlo, hhi⟩ := h
  exact ⟨hlo, fun m hm => hhi m hm⟩

/-- A typed export index satisfies the export descriptor requirement of the environment. -/
theorem external_index_valid {env : metadata.Env} {C : context} {desc : metadata.ExportDesc} {xt}
    (hc : CodeEntry.ModuleContext env C) (h : Externidx_ok C (exportIndex desc) xt) :
    ModuleSections.ExportDescValid env desc := by
  cases desc <;> cases h <;>
    simp_all [ModuleSections.ExportDescValid, hc.funcs, hc.globals, hc.tables, hc.mems, proj_uN_0]

/-- Generated typing, the module-level profile conditions and the signature limits discharge every
semantic prerequisite of the environment parser at every declaration prefix. -/
theorem profile_requirements_of_typing {profile : ValidationProfile} {raw : ModuleBinary.Module}
    (he : Elaborates raw (moduleOf raw)) (hs : SectionsTyped raw) (hp : ModuleConditions raw profile)
    (hl : ∀ ft ∈ raw.types, Itasca.Profile.FuncTypeWithinLimits ft) :
    ModuleEnv.Requirements raw profile := by
  intro id decls env hlo hhi hr
  interval_cases id
  · intro ft hm
    exact (Itasca.Profile.funcTypeAdmissible_iff profile ft).mpr ⟨hp.arity ft hm, hl ft hm⟩
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
    · intro hprofile
      have ht := hp.table_count hprofile
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
    · intro hprofile
      rw [hr.tables_count (by decide) (by decide)]
      exact hp.table_count hprofile
  · constructor
    · intro mt hm
      exact limits_scalar (by simpa [limits.MAX_MEMORY_PAGES] using memory_valid_of_typing (hs.memories mt hm))
    · rw [hr.memories_count (by decide) (by decide)]
      exact hp.memory_count
  · intro g hg
    exact global_valid_of_typing (hr.initializer_globals (by decide))
      (by simpa [ModuleConstants.FunctionContext, initializerContextOf] using hr.funcs_context (by decide)) (hs.globals g hg)
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
    exact element_valid_raw_of_typing (hr.initializer_globals (by decide))
      (by simpa [ModuleConstants.FunctionContext, initializerContextOf] using hr.funcs_context (by decide))
      (by simpa [initializerContextOf] using hr.tables_context (by decide)) (hs.elements e hm)
  · trivial

end Itasca.ModuleElaboration
