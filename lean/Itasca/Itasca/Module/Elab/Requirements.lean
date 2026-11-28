import Itasca.Module.Env.Complete
import Mathlib.Tactic.IntervalCases

open WebAssembly

/-!
# Requirements from typing

`requirements_of_typing` derives `Module.Environment.Requirements`, the semantic requirements of
every declaration section, from the generated typing of the sections, the module-level restrictions
conditions and the signature limits.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- The memory space translated from raw import types is the translation of `rawMemories`. -/
theorem raw_memories_projection (ts : List wasm_types.FuncType) (entries : List Binary.Import) :
    Module.Translation.mems (entries.map (fun e => importType ts e.desc)) =
      (Module.Sections.rawMemories entries).map Translation.Environment.memType := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [Module.Sections.rawMemories, importType] at ih
    cases hd : e.desc <;> simp [Module.Translation.mems, importType, Module.Sections.rawMemories, hd, ih]

/-- Limits valid in the SpecTec sense are valid in the binary sense for the same bound. -/
theorem limits_scalar {lim : wasm_types.Limits} {bound : U32}
    (h : Module.Translation.LimitsValid lim bound.val) : Binary.LimitsValid lim bound := by
  obtain ⟨hlo, hhi⟩ := h
  exact ⟨hlo, fun m hm => hhi m hm⟩

/-- Every function descriptor in the completed function space has an elaborated type index. -/
theorem descriptor_indices_of_elaboration {raw last decls env}
    (ready : Module.Environment.Ready raw last decls env) (doneFuncs : 3 ≤ last)
    (helab : Elaborates raw (moduleOf raw)) : Module.Environment.DescriptorIndices env.code := by
  intro d mem
  have member := List.mem_map_of_mem (f := metadata.FuncDesc.type_index) mem
  rw [ready.represents.cache.funcs, ready.imports (by omega), ready.functions doneFuncs] at member
  rw [ready.types_eq (by omega)]
  rcases List.mem_append.mp member with imported | defined
  · obtain ⟨entry, he, eq⟩ := List.mem_filterMap.mp imported
    cases hd : entry.desc <;> simp [hd] at eq
    exact eq ▸ helab.imports entry he _ hd
  · exact helab.functions _ defined

/-- A typed export index satisfies the export descriptor requirement of the environment. -/
theorem external_index_valid {env : metadata.CodeMetadata} {C : context} {desc : metadata.ExportDesc} {xt}
    (hc : CodeEntry.ModuleContext env C) (valid : Module.Environment.DescriptorIndices env)
    (h : Externidx_ok C (exportIndex desc) xt) : Module.Sections.ExportDescValid env desc := by
  cases desc with
  | Func idx =>
    cases h
    have hi : idx.val < env.funcs.val.length := by simpa [hc.funcs, proj_uN_0] using (show proj_uN_0 (.mk_uN idx.val) < C.FUNCS.length by assumption)
    have ht := valid _ (List.getElem_mem (l := env.funcs.val) hi)
    simp [Module.Sections.ExportDescValid, metadata.CodeMetadata.externalTypeAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem ht]
  | Memory idx =>
    cases h
    have hi : idx.val < env.memories.val.length := by simpa [hc.mems, proj_uN_0] using (show proj_uN_0 (.mk_uN idx.val) < C.MEMS.length by assumption)
    simp [Module.Sections.ExportDescValid, metadata.CodeMetadata.externalTypeAt, List.getElem?_eq_getElem hi]
  | Global idx =>
    cases h
    have hi : idx.val < env.globals.val.length := by simpa [hc.globals, proj_uN_0] using (show proj_uN_0 (.mk_uN idx.val) < C.GLOBALS.length by assumption)
    simp [Module.Sections.ExportDescValid, metadata.CodeMetadata.externalTypeAt, List.getElem?_eq_getElem hi]
  | Table idx =>
    cases h
    have hi : idx.val < env.tables.val.length := by simpa [hc.tables, proj_uN_0] using (show proj_uN_0 (.mk_uN idx.val) < C.TABLES.length by assumption)
    simp [Module.Sections.ExportDescValid, metadata.CodeMetadata.externalTypeAt, List.getElem?_eq_getElem hi]

/-- Generated typing, the module-level restrictions and the signature limits discharge every
semantic prerequisite of the environment parser at every declaration prefix. -/
theorem requirements_of_typing {raw : Binary.Module}
    (he : Elaborates raw (moduleOf raw)) (hs : SectionsTyped raw) (hp : ModuleConditions raw)
    (hl : ∀ ft ∈ raw.types, Itasca.CodeEntry.FuncTypeWithinLimits ft) :
    Module.Environment.Requirements raw := by
  intro id decls env hlo hhi hr
  interval_cases id
  · intro ft hm
    exact hl ft hm
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
    · have hm := hp.memory_count
      simpa [hr.empty_memories (by decide), raw_memories_projection] using
        (show (Module.Translation.mems (raw.imports.map (fun e => importType raw.types e.desc))).length ≤ 1 by omega)
  · intro idx hi
    rw [hr.types_eq (by decide)]
    exact he.functions idx hi
  · intro tt ht
    exact limits_scalar (by simpa [limits.MAX_TABLE_ELEMS, U32.rMax] using table_valid_of_typing (hs.tables tt ht))
  · constructor
    · intro mt hm
      exact limits_scalar (by simpa [limits.MAX_MEMORY_PAGES] using memory_valid_of_typing (hs.memories mt hm))
    · rw [hr.memories_count (by decide) (by decide)]
      exact hp.memory_count
  · intro g hg
    exact global_valid_of_typing (hr.initializer_globals (by decide))
      (by simpa [Module.Constants.FunctionContext, initializerContextOf] using hr.funcs_context (by decide)) (hs.globals g hg)
  · constructor
    · have hn : ((raw.exports.map Binary.Export.name).map Binary.nameOfBytes).Nodup := by
        simpa [List.map_map, Function.comp_def] using hp.unique_exports
      exact List.Nodup.of_map Binary.nameOfBytes hn
    · intro e mem
      obtain ⟨xt, ht⟩ := hs.exports e mem
      have hx : Externidx_ok (contextOf raw) (exportIndex e.desc) xt := by cases ht; assumption
      exact external_index_valid (hr.module_context (by decide)) (descriptor_indices_of_elaboration hr (by decide) he) hx
  · intro idx hi
    exact start_valid_of_typing (hr.module_context (by decide)) (descriptor_indices_of_elaboration hr (by decide) he) (hs.start idx hi)
  · intro e hm
    exact element_valid_raw_of_typing (hr.initializer_globals (by decide))
      (by simpa [Module.Constants.FunctionContext, initializerContextOf] using hr.funcs_context (by decide))
      (by simpa [initializerContextOf] using hr.tables_context (by decide)) (hs.elements e hm)
  · trivial

end Itasca.Module.Elaboration
