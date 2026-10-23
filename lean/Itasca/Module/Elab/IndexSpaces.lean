import Itasca.Module.Elab.ExternalTyping

/-!
# Index spaces of the elaborated module

`importTypes` gives the SpecTec external types of the imports. The `_imports` lemmas relate the
translated import spaces to the environment's `importedFuncs`, `importedGlobals`, `importedTables`
and `importedMems`, and the `_cache` lemmas show the translated merged caches are imports followed
by definitions. `moduleContext` and `initializerContext` are the contexts used for the generated
judgments.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The SpecTec external types of the environment's imports, in order. -/
def importTypes (env : module.Env) : List externtype :=
  env.imports.val.map (fun entry => importType env.types.val entry.desc)

/-- The function space translated from import types is the translation of `importedFuncs`. -/
theorem funcs_imports (types : List types.FuncType) (entries : List module.Import) :
    ModuleTranslation.funcs (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedFuncs entries).map (functionType types) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedFuncs, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.funcs, importType, ModuleEnv.importedFuncs, hd, ih]

/-- The global space translated from import types is the translation of `importedGlobals`. -/
theorem globals_imports (types : List types.FuncType) (entries : List module.Import) :
    ModuleTranslation.globals (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedGlobals entries).map Translate.globalType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedGlobals, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.globals, importType, ModuleEnv.importedGlobals, hd, ih]

/-- The table space translated from import types is the translation of `importedTables`. -/
theorem tables_imports (types : List types.FuncType) (entries : List module.Import) :
    ModuleTranslation.tables (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedTables entries).map EnvTranslation.tableType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedTables, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.tables, importType, ModuleEnv.importedTables, hd, ih]

/-- The memory space translated from import types is the translation of `importedMems`. -/
theorem mems_imports (types : List types.FuncType) (entries : List module.Import) :
    ModuleTranslation.mems (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedMems entries).map EnvTranslation.memType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedMems, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.mems, importType, ModuleEnv.importedMems, hd, ih]

/-- Resolved type indices translate to the translated function types. -/
theorem resolved_functions {types indices fts}
    (h : List.Forall₂ (ModuleEnv.Resolves types) indices fts) :
    indices.map (functionType types) = fts.map EnvTranslation.funcType := by
  induction h with
  | nil => rfl
  | cons hf _ ih =>
    obtain ⟨hi, he⟩ := hf
    simp [functionType_lookup hi, he, ih]

/-- The translated function cache is the imported functions followed by the defined ones. -/
theorem funcs_cache {env tables memories} (h : ModuleEnv.Cache env tables memories) :
    env.func_types.val.map EnvTranslation.funcType = ModuleTranslation.funcs (importTypes env) ++
      env.func_type_indices.val.map (functionType env.types.val) := by
  rw [importTypes, funcs_imports]
  simpa using (resolved_functions h.funcs).symm

/-- The translated global cache is the imported globals followed by the defined ones. -/
theorem globals_cache {env tables memories} (h : ModuleEnv.Cache env tables memories) :
    env.global_types.val.map Translate.globalType = ModuleTranslation.globals (importTypes env) ++
      env.globals.val.map (fun g => Translate.globalType g.gtype) := by
  simp [importTypes, globals_imports, h.globals, List.map_append, List.map_map]

/-- The translated table cache is the imported tables followed by the defined ones. -/
theorem tables_cache {env tables memories} (h : ModuleEnv.Cache env tables memories) :
    env.table_types.val.map EnvTranslation.tableType = ModuleTranslation.tables (importTypes env) ++
      tables.map EnvTranslation.tableType := by
  simp [importTypes, tables_imports, h.tables, List.map_append]

/-- The translated memory cache is the imported memories followed by the defined ones. -/
theorem memories_cache {env tables memories} (h : ModuleEnv.Cache env tables memories) :
    env.mem_types.val.map EnvTranslation.memType = ModuleTranslation.mems (importTypes env) ++
      memories.map EnvTranslation.memType := by
  simp [importTypes, mems_imports, h.memories, List.map_append]

/-- The typing context for functions, elements, segments and exports: the environment's translated
index spaces, the given element types and `dataCount` data segments, and no locals or labels. -/
def moduleContext (env : module.Env) (elementTypes : List elemtype) (dataCount : Nat) : context :=
  { TYPES := env.types.val.map EnvTranslation.funcType
    FUNCS := env.func_types.val.map EnvTranslation.funcType
    GLOBALS := env.global_types.val.map Translate.globalType
    TABLES := env.table_types.val.map EnvTranslation.tableType
    MEMS := env.mem_types.val.map EnvTranslation.memType
    ELEMS := elementTypes
    DATAS := List.replicate dataCount datatype.OK
    LOCALS := []
    LABELS := []
    RETURN := none }

/-- The typing context for constant initializers: `moduleContext` with no segment spaces and only
the imported globals. -/
def initializerContext (env : module.Env) : context :=
  { moduleContext env [] 0 with
    GLOBALS := (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType }

/-- `moduleContext` is a `CodeEntry.ModuleContext` for the environment. -/
theorem moduleContext_matches (env : module.Env) (elementTypes : List elemtype) (dataCount : Nat) :
    CodeEntry.ModuleContext env (moduleContext env elementTypes dataCount) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `moduleContext` is well formed. -/
theorem moduleContext_wf (env : module.Env) (elementTypes : List elemtype) (dataCount : Nat) :
    wf_context (moduleContext env elementTypes dataCount) :=
  (moduleContext_matches env elementTypes dataCount).wf

/-- `initializerContext` is well formed. -/
theorem initializerContext_wf (env : module.Env) : wf_context (initializerContext env) := by
  cases moduleContext_wf env [] 0
  constructor <;> assumption

end Itasca.ModuleElaboration
