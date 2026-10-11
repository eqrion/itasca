import Itasca.Module.ModuleEnvRequirements
import Itasca.Module.ModuleSectionInversion

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleElaboration

theorem Ready.types_eq {raw last decls env} (h : Ready raw last decls env) (hn : 1 ≤ last) :
    env.types.val = raw.types := h.represents.types.symm.trans (h.types hn)

theorem Ready.imports_eq {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    env.imports.val.map rawImport = raw.imports := h.represents.imports.symm.trans (h.imports hn)

theorem Ready.functions_eq {raw last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    env.func_type_indices.val = raw.functions := h.represents.functions.symm.trans (h.functions hn)

theorem Ready.globals_eq {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    env.globals.val = raw.globals := h.represents.globals.symm.trans (h.globals hn)

theorem Ready.elements_eq {raw last decls env} (h : Ready raw last decls env) (hn : 9 ≤ last) :
    env.elements.val.map rawElement = raw.elements := h.represents.elements.symm.trans (h.elements hn)

theorem Ready.dataCount_eq {raw last decls env} (h : Ready raw last decls env) (hn : 10 ≤ last) :
    env.data_count = raw.dataCount := h.represents.dataCount.symm.trans (h.dataCount hn)

theorem Ready.elements_context {raw last decls env} (h : Ready raw last decls env) (hn : 9 ≤ last) :
    (contextOf raw).ELEMS = EnvTranslation.elementTypes env := by
  simp only [contextOf]
  rw [← h.elements_eq hn]
  simp [EnvTranslation.elementTypes, rawElement, List.map_map]

/-- An encoded data count identifies the final data space. When omitted, the
independent binary condition rules out every data-index instruction in each body. -/
theorem Ready.data_context {raw last decls env} (h : Ready raw last decls env) (hn : 10 ≤ last)
    (hv : ModuleBinary.DataCountValid raw) (entry : ModuleBinary.Code) (hm : entry ∈ raw.codes) :
    (contextOf raw).DATAS = EnvTranslation.dataTypes env ∨ ModuleBinary.instructionsUseData entry.body = false := by
  cases hc : raw.dataCount with
  | none =>
    right
    exact (show ∀ code ∈ raw.codes, ModuleBinary.instructionsUseData code.body = false from by
      simpa only [ModuleBinary.DataCountValid, hc] using hv) entry hm
  | some count =>
    left
    have he : count.val = raw.data.length := by simpa only [ModuleBinary.DataCountValid, hc] using hv
    simp [contextOf, EnvTranslation.dataTypes, h.dataCount_eq hn, hc, he]

theorem Ready.importTypes_eq {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    importTypes env = raw.imports.map (fun e => importType raw.types e.desc) := by
  rw [← h.imports_eq hn]
  simp [importTypes, h.types_eq (by omega), List.map_map, rawImport, Function.comp_def]

theorem Ready.funcs_context {raw last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    (contextOf raw).FUNCS = env.func_types.val.map EnvTranslation.funcType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.functions_eq hn, h.types_eq (by omega)] using funcs_cache h.represents.cache

theorem Ready.tables_context {raw last decls env} (h : Ready raw last decls env) (hn : 4 ≤ last) :
    (contextOf raw).TABLES = env.table_types.val.map EnvTranslation.tableType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.tables hn] using tables_cache h.represents.cache

theorem Ready.memories_context {raw last decls env} (h : Ready raw last decls env) (hn : 5 ≤ last) :
    (contextOf raw).MEMS = env.mem_types.val.map EnvTranslation.memType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.memories hn] using memories_cache h.represents.cache

theorem Ready.globals_context {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    (contextOf raw).GLOBALS = env.global_types.val.map Translate.globalType := by
  symm
  simpa [contextOf, h.importTypes_eq (by omega), h.globals_eq hn] using globals_cache h.represents.cache

theorem Ready.moduleContext {raw last decls env} (h : Ready raw last decls env) (hn : 6 ≤ last) :
    CodeEntry.ModuleContext env (contextOf raw) :=
  ⟨by simp [contextOf, h.types_eq (by omega)], h.funcs_context (by omega),
    h.globals_context hn, h.tables_context (by omega), h.memories_context (by omega), rfl, rfl⟩

theorem Ready.initializer_globals {raw last decls env} (h : Ready raw last decls env) (hn : 2 ≤ last) :
    ModuleConstants.GlobalContext env (initializerContextOf raw) := by
  change ModuleTranslation.globals (raw.imports.map (fun e => importType raw.types e.desc)) = _
  rw [← h.importTypes_eq hn, importTypes, globals_imports, h.represents.cache.global_prefix]

theorem Ready.empty_imports {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.imports.val = [] := by
  have hp := h.phase.2.1 hn
  exact List.map_eq_nil_iff.mp (h.represents.imports.symm.trans hp)

theorem Ready.future_tables {raw last decls env} (h : Ready raw last decls env) (hn : last < 4) :
    decls.tables = [] := h.phase.2.2.2.1 hn

theorem Ready.future_memories {raw last decls env} (h : Ready raw last decls env) (hn : last < 5) :
    decls.memories = [] := h.phase.2.2.2.2.1 hn

theorem Ready.empty_tables {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.table_types.val = [] := by
  simp [h.represents.cache.tables, h.empty_imports hn, h.future_tables (by omega), importedTables]

theorem Ready.empty_memories {raw last decls env} (h : Ready raw last decls env) (hn : last < 2) :
    env.mem_types.val = [] := by
  simp [h.represents.cache.memories, h.empty_imports hn, h.future_memories (by omega), importedMems]

theorem Ready.tables_count {raw last decls env} (h : Ready raw last decls env)
    (hlo : 2 ≤ last) (hhi : last < 4) :
    env.table_types.val.length =
      (ModuleTranslation.tables (raw.imports.map (fun e => importType raw.types e.desc))).length := by
  rw [← h.importTypes_eq hlo, importTypes, tables_imports, List.length_map,
    h.represents.cache.tables, h.future_tables hhi, List.append_nil]

theorem Ready.memories_count {raw last decls env} (h : Ready raw last decls env)
    (hlo : 2 ≤ last) (hhi : last < 5) :
    env.mem_types.val.length =
      (ModuleTranslation.mems (raw.imports.map (fun e => importType raw.types e.desc))).length := by
  rw [← h.importTypes_eq hlo, importTypes, mems_imports, List.length_map,
    h.represents.cache.memories, h.future_memories hhi, List.append_nil]

end Itasca.ModuleEnv
