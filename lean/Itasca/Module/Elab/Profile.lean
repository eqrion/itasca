import Itasca.Module.Env.Encoding
import Itasca.Binary.UnicodeUnique
import Itasca.Module.Code.Encoding
import Itasca.Module.Elab.SegmentTyping
import Itasca.Support.Result
import Mathlib.Data.List.Nodup

/-!
Sections, each formerly its own module: Elaboration, ExternalTyping, IndexSpaces, ElementTyping, TypingLists, Assembly, Declared, Profile.
-/

/-! ## Elaboration -/

section

/-!
# Elaboration of raw modules

`moduleOf` translates a raw `ModuleBinary.Module` into the SpecTec `module` syntax, expanding the
binary representation's indexed forms. `Elaborates` relates a SpecTec module to a raw one, and
`ModuleConditions` states the module-level restrictions that the generated 2.0 judgment lacks.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The SpecTec type of function type index `idx`, with an empty type as the fallback that makes
the translation total. `Elaborates` requires every type reference to be in bounds, so no accepted
module uses the fallback. -/
def functionType (types : List wasm_types.FuncType) (idx : U32) : functype :=
  ((types[idx.val]?).map EnvTranslation.funcType).getD (.mk_functype (.mk_list []) (.mk_list []))

/-- An in-bounds type index looks up its translated function type. -/
theorem functionType_lookup {types : List wasm_types.FuncType} {idx : U32}
    (hi : idx.val < types.length) :
    functionType types idx = EnvTranslation.funcType types[idx.val] := by
  simp [functionType, List.getElem?_eq_getElem hi]

/-- The SpecTec external type of an import descriptor. -/
def importType (types : List wasm_types.FuncType) : metadata.ImportDesc → externtype
  | .Func idx => .FUNC (functionType types idx)
  | .Table tt => .TABLE (EnvTranslation.tableType tt)
  | .Memory mt => .MEM (EnvTranslation.memType mt)
  | .Global gt => .GLOBAL (Translate.globalType gt)

/-- The SpecTec import declaration of a raw import. -/
def importDecl (types : List wasm_types.FuncType) (entry : ModuleBinary.Import) : «import» :=
  .IMPORT (ModuleBinary.nameOfBytes entry.moduleName) (ModuleBinary.nameOfBytes entry.name)
    (importType types entry.desc)

/-- The SpecTec external index of an export descriptor. -/
def exportIndex : metadata.ExportDesc → externidx
  | .Func idx => .FUNC (.mk_uN idx.val)
  | .Table idx => .TABLE (.mk_uN idx.val)
  | .Memory idx => .MEM (.mk_uN idx.val)
  | .Global idx => .GLOBAL (.mk_uN idx.val)

/-- The SpecTec export declaration of a raw export. -/
def exportDecl (entry : ModuleBinary.Export) : «export» :=
  .EXPORT (ModuleBinary.nameOfBytes entry.name) (exportIndex entry.desc)

/-- The SpecTec element segment of a raw element segment. -/
def element (entry : ModuleBinary.Element) : elem :=
  .ELEM (Translate.referenceType entry.elem) (entry.init.map ModuleConstants.expression)
    (ModuleSegments.elementMode entry.mode)

/-- The SpecTec table of a table type. -/
def table (tt : wasm_types.TableType) : _root_.table := .TABLE (EnvTranslation.tableType tt)

/-- The SpecTec memory of a memory type. -/
def memory (mt : wasm_types.MemType) : mem := .MEMORY (EnvTranslation.memType mt)

/-- The SpecTec start function of a function index. -/
def start (idx : U32) : _root_.start := .START (.mk_uN idx.val)

/-- The SpecTec module of a raw module. It keeps the decoded declarations, the ordered exports and
the exact function bodies, and only expands the binary representation's indexed forms. -/
def moduleOf (raw : ModuleBinary.Module) : _root_.module :=
  .MODULE (raw.types.map (fun ft => .TYPE (EnvTranslation.funcType ft)))
    (raw.imports.map (importDecl raw.types))
    (List.zipWith CodeEntry.function raw.functions raw.codes)
    (raw.globals.map ModuleConstants.global) (raw.tables.map table) (raw.memories.map memory)
    (raw.elements.map element) (raw.data.map ModuleData.translate) (raw.start.map start)
    (raw.exports.map exportDecl)

/-- `spec` is the elaboration of `raw`. No validator call occurs in elaboration. The index bounds
exclude fallback lookups, and the count equality excludes truncation by `zipWith`. -/
structure Elaborates (raw : ModuleBinary.Module) (spec : _root_.module) : Prop where
  module_eq : spec = moduleOf raw
  imports : ∀ entry ∈ raw.imports, ∀ idx, entry.desc = .Func idx → idx.val < raw.types.length
  functions : ∀ idx ∈ raw.functions, idx.val < raw.types.length
  code_count : raw.functions.length = raw.codes.length

/-- The module-level conditions that `Module_ok` does not express: unique export names, the
at most one memory.
Instruction syntax itself is restricted by `ModuleBinary`. -/
structure ModuleConditions (raw : ModuleBinary.Module) : Prop where
  unique_exports : (raw.exports.map (fun entry => ModuleBinary.nameOfBytes entry.name)).Nodup
  memory_count : (ModuleTranslation.mems (raw.imports.map (fun entry => importType raw.types entry.desc))).length +
    raw.memories.length ≤ 1

end Itasca.ModuleElaboration

end

/-! ## ExternalTyping -/

section

/-!
# Typing of imports, exports and the start function

Generated typing judgments (`Import_ok`, `Export_ok`, `Externidx_ok`, `Start_ok`) for the imports,
exports and start function of a valid cached environment. `import_typed` and `export_typed` give
the external type that `ModuleExternals.ImportResolves` and `ExportResolves` describe.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The SpecTec translation of an external type is well formed. -/
theorem externalType_wf (xt : wasm_types.ExternType) : wf_externtype (ModuleExternals.externalType xt) := by
  cases xt with
  | Func ft => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (EnvTranslation.tableType_wf tt)
  | Memory mt => exact .externtype_case_3 _ (EnvTranslation.memType_wf mt)

/-- The SpecTec external index of an export descriptor is well formed. -/
theorem exportIndex_wf (desc : metadata.ExportDesc) : wf_externidx (exportIndex desc) := by
  cases desc with
  | Func idx => exact .externidx_case_0 _ (EnvTranslation.index_wf idx)
  | Table idx => exact .externidx_case_2 _ (EnvTranslation.index_wf idx)
  | Memory idx => exact .externidx_case_3 _ (EnvTranslation.index_wf idx)
  | Global idx => exact .externidx_case_1 _ (EnvTranslation.index_wf idx)

/-- A resolved import has the translated external type as its `importType`. -/
theorem importType_resolved {env : metadata.Env} {entry : metadata.Import} {xt : wasm_types.ExternType}
    (h : ModuleExternals.ImportResolves env entry xt) :
    importType env.types.val entry.desc = ModuleExternals.externalType xt := by
  cases hd : entry.desc with
  | Func idx =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    simp [importType, ModuleExternals.externalType, functionType_lookup hi]
  | Table tt =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    simp [h, importType, ModuleExternals.externalType]
  | Memory mt =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    simp [h, importType, ModuleExternals.externalType]
  | Global gt =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    simp [h, importType, ModuleExternals.externalType]

/-- A resolved export index has the translated external type in the module context. -/
theorem export_index_typed {env : metadata.Env} {entry : metadata.Export} {xt : wasm_types.ExternType}
    (h : ModuleExternals.ExportResolves env entry xt)
    (C : context) (hC : CodeEntry.ModuleContext env C) :
    Externidx_ok C (exportIndex entry.desc) (ModuleExternals.externalType xt) := by
  cases hd : entry.desc with
  | Func idx =>
    simp only [ModuleExternals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.func C _ _
    · simpa [hC.funcs, proj_uN_0] using hi
    · simp only [hC.funcs, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using exportIndex_wf entry.desc
    · exact .externtype_case_0 _
  | Table idx =>
    simp only [ModuleExternals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.table C _ _
    · simpa [hC.tables, proj_uN_0] using hi
    · simp only [hC.tables, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using exportIndex_wf entry.desc
    · exact .externtype_case_2 _ (EnvTranslation.tableType_wf _)
  | Memory idx =>
    simp only [ModuleExternals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.mem C _ _
    · simpa [hC.mems, proj_uN_0] using hi
    · simp only [hC.mems, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using exportIndex_wf entry.desc
    · exact .externtype_case_3 _ (EnvTranslation.memType_wf _)
  | Global idx =>
    simp only [ModuleExternals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.global C _ _
    · simpa [hC.globals, proj_uN_0] using hi
    · simp only [hC.globals, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using exportIndex_wf entry.desc
    · exact .externtype_case_1 _

/-- A resolved export with a well-formed name is typed in the module context. -/
theorem export_typed {env : metadata.Env} {entry : metadata.Export} {xt : wasm_types.ExternType}
    (h : ModuleExternals.ExportResolves env entry xt)
    (hn : wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (C : context) (hC : CodeEntry.ModuleContext env C) :
    Export_ok C (exportDecl (ModuleEnv.rawExport entry)) (ModuleExternals.externalType xt) := by
  exact .mk_Export_ok C _ _ _ (export_index_typed h C hC) hC.wf (externalType_wf xt)
    (.export_case_0 _ _ hn (exportIndex_wf entry.desc))

/-- `functionType` always gives a valid function type. -/
theorem functionType_valid (types : List wasm_types.FuncType) (idx : U32) :
    Functype_ok (functionType types idx) := by
  cases he : types[idx.val]? with
  | none => simp only [functionType, he, Option.map_none, Option.getD_none]; constructor
  | some ft => simpa [functionType, he] using ModuleTranslation.funcType_valid ft

/-- An import's SpecTec external type is well formed. -/
theorem importType_wf (types : List wasm_types.FuncType) (desc : metadata.ImportDesc) :
    wf_externtype (importType types desc) := by
  cases desc with
  | Func idx => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (EnvTranslation.tableType_wf tt)
  | Memory mt => exact .externtype_case_3 _ (EnvTranslation.memType_wf mt)

/-- The external type of each import of a valid cached environment is valid. -/
theorem import_type_valid {env : metadata.Env} {tables memories entry}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (he : entry ∈ env.imports.val) : Externtype_ok (importType env.types.val entry.desc) := by
  cases hd : entry.desc with
  | Func idx => exact .func _ (functionType_valid _ _) (.externtype_case_0 _)
  | Global gt => exact .global _ (Translate.globalType_valid gt) (.externtype_case_1 _)
  | Table tt =>
    have hi : tt ∈ ModuleEnv.importedTables env.imports.val := by
      simp only [ModuleEnv.importedTables, List.mem_filterMap]
      exact ⟨entry, he, by simp [hd]⟩
    have ht : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_left _ hi
    exact .table _ (ModuleTranslation.tableType_valid tt (hv.tables tt ht))
      (.externtype_case_2 _ (EnvTranslation.tableType_wf tt))
  | Memory mt =>
    have hi : mt ∈ ModuleEnv.importedMems env.imports.val := by
      simp only [ModuleEnv.importedMems, List.mem_filterMap]
      exact ⟨entry, he, by simp [hd]⟩
    have ht : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_left _ hi
    exact .mem _ (ModuleTranslation.memType_valid mt (hv.memories mt ht))
      (.externtype_case_3 _ (EnvTranslation.memType_wf mt))

/-- Each import of a valid cached environment is typed, given well-formed names. -/
theorem import_typed {env : metadata.Env} {tables memories entry}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (he : entry ∈ env.imports.val)
    (hmod : wf_name (ModuleBinary.nameOfBytes entry.module.val))
    (hn : wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (C : context) (hC : wf_context C) :
    Import_ok C (importDecl env.types.val (ModuleEnv.rawImport entry))
      (importType env.types.val entry.desc) := by
  exact .mk_Import_ok C _ _ _ (import_type_valid hc hv he) hC
    (.import_case_0 _ _ _ hmod hn (importType_wf _ _))

/-- The start function of a valid environment is typed in the module context. -/
theorem start_typed {env : metadata.Env} (hv : ModuleEnv.Valid env) (idx : U32)
    (hs : env.start = some idx) (C : context) (hC : CodeEntry.ModuleContext env C) :
    Start_ok C (start idx) := by
  obtain ⟨hi, hp, hr⟩ := hv.start idx hs
  apply Start_ok.mk_Start_ok C _
  · simpa [hC.funcs, proj_uN_0] using hi
  · simp only [hC.funcs, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    simp [EnvTranslation.funcType, hp, hr]
  · exact hC.wf
  · exact .start_case_0 _ (EnvTranslation.index_wf idx)

end Itasca.ModuleElaboration

end

/-! ## IndexSpaces -/

section

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
def importTypes (env : metadata.Env) : List externtype :=
  env.imports.val.map (fun entry => importType env.types.val entry.desc)

/-- The function space translated from import types is the translation of `importedFuncs`. -/
theorem funcs_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    ModuleTranslation.funcs (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedFuncs entries).map (functionType types) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedFuncs, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.funcs, importType, ModuleEnv.importedFuncs, hd, ih]

/-- The global space translated from import types is the translation of `importedGlobals`. -/
theorem globals_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    ModuleTranslation.globals (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedGlobals entries).map Translate.globalType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedGlobals, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.globals, importType, ModuleEnv.importedGlobals, hd, ih]

/-- The table space translated from import types is the translation of `importedTables`. -/
theorem tables_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    ModuleTranslation.tables (entries.map (fun entry => importType types entry.desc)) =
      (ModuleEnv.importedTables entries).map EnvTranslation.tableType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [ModuleEnv.importedTables, importType] at ih
    cases hd : entry.desc <;>
      simp [ModuleTranslation.tables, importType, ModuleEnv.importedTables, hd, ih]

/-- The memory space translated from import types is the translation of `importedMems`. -/
theorem mems_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
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
def moduleContext (env : metadata.Env) (elementTypes : List elemtype) (dataCount : Nat) : context :=
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
def initializerContext (env : metadata.Env) : context :=
  { moduleContext env [] 0 with
    GLOBALS := (env.global_types.val.take env.num_imported_globals.val).map Translate.globalType }

/-- `moduleContext` is a `CodeEntry.ModuleContext` for the environment. -/
theorem moduleContext_matches (env : metadata.Env) (elementTypes : List elemtype) (dataCount : Nat) :
    CodeEntry.ModuleContext env (moduleContext env elementTypes dataCount) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `moduleContext` is well formed. -/
theorem moduleContext_wf (env : metadata.Env) (elementTypes : List elemtype) (dataCount : Nat) :
    wf_context (moduleContext env elementTypes dataCount) :=
  (moduleContext_matches env elementTypes dataCount).wf

/-- `initializerContext` is well formed. -/
theorem initializerContext_wf (env : metadata.Env) : wf_context (initializerContext env) := by
  cases moduleContext_wf env [] 0
  constructor <;> assumption

end Itasca.ModuleElaboration

end

/-! ## ElementTyping -/

section

/-!
# Element, table and memory typing

Generated typing judgments (`Elem_ok`, `Table_ok`, `Mem_ok`) for the elements, tables and
memories of a valid cached environment, in the initializer context, and the `ref.func` constant
expression used by function reference initializers.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- Each element segment of a valid environment is typed in the initializer context. -/
theorem element_typed {env : metadata.Env} (hv : ModuleEnv.Valid env)
    (entry : metadata.Element) (he : entry ∈ env.elements.val) :
    Elem_ok (initializerContext env) (element (ModuleEnv.rawElement entry))
      (Translate.referenceType entry.elem) := by
  exact (hv.elements entry he).typed (initializerContext env) (initializerContext_wf env)
    rfl rfl rfl

/-- Each defined table of a valid cached environment is typed in any well-formed context. -/
theorem table_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
     (hv : ModuleEnv.Valid env) (tt : wasm_types.TableType) (ht : tt ∈ tables)
    (C : context) (hC : wf_context C) :
    Table_ok C (table tt) (EnvTranslation.tableType tt) := by
  have hm : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_right _ ht
  exact .mk_Table_ok C _ (ModuleTranslation.tableType_valid tt (hv.tables tt hm)) hC
    (.table_case_0 _ (EnvTranslation.tableType_wf tt))

/-- Each defined memory of a valid cached environment is typed in any well-formed context. -/
theorem memory_typed {env tables memories} (hc : ModuleEnv.Cache env tables memories)
     (hv : ModuleEnv.Valid env) (mt : wasm_types.MemType) (ht : mt ∈ memories)
    (C : context) (hC : wf_context C) :
    Mem_ok C (memory mt) (EnvTranslation.memType mt) := by
  have hm : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_right _ ht
  exact .mk_Mem_ok C _ (ModuleTranslation.memType_valid mt (hv.memories mt hm)) hC
    (.mem_case_0 _ (EnvTranslation.memType_wf mt))

end Itasca.ModuleElaboration

end

/-! ## TypingLists -/

section

/-!
# Typing of lists of declarations

List-level versions of the per-declaration typing results. `functions_typed` types the code entries
as `Func_ok` and `exports_typed` types the exports. Small helpers convert between the generated
`Forall₂` and `List.Forall₂`, and the `.wf` theorems extract well-formedness from the typing
judgments.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- `List.Forall₂` gives the generated `Forall₂`. -/
theorem forall₂_generated {α β : Type} {R : α → β → Prop} {xs ys}
    (h : List.Forall₂ R xs ys) : Forall₂ R xs ys := by
  induction h with
  | nil => simp [Forall₂]
  | cons hp _ ih => simpa [Forall₂] using And.intro hp ih

theorem forall₂_map {α β γ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (R : β → γ → Prop) (h : ∀ a ∈ xs, R (f a) (g a)) :
    List.Forall₂ R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih (by intro a ha; exact h a (by simp [ha])))

theorem forall₂_left {α β : Type} {R : α → β → Prop} {xs ys}
    (h : List.Forall₂ R xs ys) (P : α → Prop) (hp : ∀ a b, R a b → P a) : Forall P xs := by
  induction h with
  | nil => simp [Forall]
  | cons hr _ ih => simpa [Forall] using And.intro (hp _ _ hr) ih

theorem forall₂_right {α β : Type} {R : α → β → Prop} {xs ys}
    (h : List.Forall₂ R xs ys) (P : β → Prop) (hp : ∀ a b, R a b → P b) : Forall P ys := by
  induction h with
  | nil => simp [Forall]
  | cons hr _ ih => simpa [Forall] using And.intro (hp _ _ hr) ih

/-- Pointwise `Typed` code entries are typed as functions in a module context, at the function types
of their type indices. -/
theorem functions_typed {env indices codes}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) indices codes)
    (C : context) (hc : CodeEntry.ModuleContext env C)
    (hsegments : CodeEntry.SegmentContext env C) :
    List.Forall₂ (fun ft f => Func_ok C f ft)
      (indices.map (functionType env.types.val)) (List.zipWith CodeEntry.function indices codes) := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
    apply List.Forall₂.cons _ ih
    simpa [functionType_lookup hp.type_lt] using hp.func_ok C hc hsegments

/-- Resolved exports with well-formed names are typed in a module context. -/
theorem exports_typed {env entries xts}
    (h : List.Forall₂ (ModuleExternals.ExportResolves env) entries xts)
    (hn : ∀ entry ∈ entries, wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (C : context) (hc : CodeEntry.ModuleContext env C) :
    List.Forall₂ (Export_ok C) (entries.map (fun e => exportDecl (ModuleEnv.rawExport e)))
      (xts.map ModuleExternals.externalType) := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
    exact .cons (export_typed hp (hn _ (by simp)) C hc)
      (ih (by intro e he; exact hn e (by simp [he])))

theorem Func_ok.wf {C f ft} (h : Func_ok C f ft) : wf_func f := by cases h; assumption
theorem Global_ok.wf {C g gt} (h : Global_ok C g gt) : wf_global g := by cases h; assumption
theorem Table_ok.wf {C t tt} (h : Table_ok C t tt) : wf_table t := by cases h; assumption
theorem Mem_ok.wf {C m mt} (h : Mem_ok C m mt) : wf_mem m := by cases h; assumption
theorem Elem_ok.wf {C e rt} (h : Elem_ok C e rt) : wf_elem e := by cases h; assumption
theorem Data_ok.wf {C d} (h : Data_ok C d) : wf_data d := by cases h; assumption
theorem Import_ok.wf {C i xt} (h : Import_ok C i xt) : wf_import i := by cases h; assumption
theorem Export_ok.wf {C e xt} (h : Export_ok C e xt) : wf_export e := by cases h; assumption
theorem Export_ok.type_wf {C e xt} (h : Export_ok C e xt) : wf_externtype xt := by cases h; assumption
theorem Start_ok.wf {C s} (h : Start_ok C s) : wf_start s := by cases h; assumption

end Itasca.ModuleElaboration

end

/-! ## Assembly -/

section

/-!
# Assembling `Module_ok`

`typed` assembles the generated section judgments (`Type_ok`, `Import_ok`, `Global_ok`,
`Table_ok`, `Mem_ok`, `Elem_ok`, `Data_ok`, `Func_ok`, `Start_ok`, `Export_ok`) into
`Module_ok` of the elaborated module in one coherent module context. `fromEnv` is the raw module
that an environment, its defined tables and memories, code entries and data segments describe.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The raw module described by an environment, its defined tables and memories, the code entries
and the data segments. -/
def fromEnv (env : metadata.Env) (tables : List wasm_types.TableType) (memories : List wasm_types.MemType)
    (codes : List ModuleBinary.Code) (segments : List metadata.Data) : ModuleBinary.Module :=
  ⟨env.types.val, env.imports.val.map ModuleEnv.rawImport, env.func_type_indices.val,
    tables, memories, env.globals.val, env.exports.val.map ModuleEnv.rawExport, env.start,
    env.elements.val.map ModuleEnv.rawElement, env.data_count, codes, segments.map ModuleData.raw⟩

/-- If the environment represents the declarations, the declarations' raw module is `fromEnv`. -/
theorem represents_module {env decls codes segments} (h : ModuleEnv.Represents env decls) :
    decls.module codes (segments.map ModuleData.raw) =
      fromEnv env decls.tables decls.memories codes segments := by
  simp [ModuleEnv.Declarations.module, fromEnv, h.types, h.imports, h.functions,
    h.globals, h.exports, h.start, h.elements, h.dataCount]

/-- The context for import typing: only the module's types. -/
def importContext (env : metadata.Env) : context :=
  ⟨env.types.val.map EnvTranslation.funcType, [], [], [], [], [], [], [], [], none⟩

/-- The import context is well formed. -/
theorem importContext_wf (env : metadata.Env) : wf_context (importContext env) := by
  constructor <;> simp [Forall]

/-- For a cached environment, `moduleContext` is the imported spaces followed by the defined
spaces, with the given element spaces and data count. -/
theorem moduleContext_eq {env tables memories} (hc : ModuleEnv.Cache env tables memories)
    (es : List elemtype) (nd : Nat) :
    moduleContext env es nd =
      ⟨env.types.val.map EnvTranslation.funcType,
        ModuleTranslation.funcs (importTypes env) ++ env.func_type_indices.val.map (functionType env.types.val),
        ModuleTranslation.globals (importTypes env) ++ env.globals.val.map (fun g => Translate.globalType g.gtype),
        ModuleTranslation.tables (importTypes env) ++ tables.map EnvTranslation.tableType,
        ModuleTranslation.mems (importTypes env) ++ memories.map EnvTranslation.memType,
        es, List.replicate nd .OK, [], [], none⟩ := by
  simp only [moduleContext, funcs_cache hc, globals_cache hc, tables_cache hc, memories_cache hc]

/-- For a cached environment, `initializerContext` has the imported globals only and no local,
label or segment spaces. -/
theorem initializerContext_eq {env tables memories} (hc : ModuleEnv.Cache env tables memories) :
    initializerContext env =
      ⟨env.types.val.map EnvTranslation.funcType,
        ModuleTranslation.funcs (importTypes env) ++ env.func_type_indices.val.map (functionType env.types.val),
        ModuleTranslation.globals (importTypes env),
        ModuleTranslation.tables (importTypes env) ++ tables.map EnvTranslation.tableType,
        ModuleTranslation.mems (importTypes env) ++ memories.map EnvTranslation.memType,
        [], [], [], [], none⟩ := by
  simp only [initializerContext, moduleContext, funcs_cache hc, tables_cache hc,
    memories_cache hc, hc.global_prefix, importTypes, globals_imports, List.replicate_zero]

/-- A valid cached environment with typed code entries, valid data segments and resolved exports
has `Module_ok` for its elaborated module. All section judgments are assembled in one coherent
module context, and name well-formedness comes from the independent byte grammar. -/
theorem typed {env : metadata.Env} {tables memories codes segments xts}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (hiNames : ∀ entry ∈ env.imports.val,
      wf_name (ModuleBinary.nameOfBytes entry.module.val) ∧ wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (heNames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (hsegments : ∀ segment ∈ segments, ModuleData.Valid env segment)
    (hdataCount : ∀ count, env.data_count = some count → count.val = segments.length)
    (hxts : List.Forall₂ (ModuleExternals.ExportResolves env) env.exports.val xts) :
    Module_ok (moduleOf (fromEnv env tables memories codes segments)) := by
  let C := moduleContext env (EnvTranslation.elementTypes env) segments.length
  let C' := initializerContext env
  have hwC := moduleContext_wf env (EnvTranslation.elementTypes env) segments.length
  have hwC' := initializerContext_wf env
  have hmatch := moduleContext_matches env (EnvTranslation.elementTypes env) segments.length
  have hsegmentContext : CodeEntry.SegmentContext env C := by
    constructor
    · simp [C, moduleContext]
    · cases hd : env.data_count with
      | none => simp [C, moduleContext, EnvTranslation.dataTypes, hd]
      | some count => simp [C, moduleContext, EnvTranslation.dataTypes, hd, hdataCount count hd]
  have htypes := forall₂_map env.types.val EnvTranslation.funcType
    (fun ft => type.TYPE (EnvTranslation.funcType ft)) (fun ft ty => Type_ok ty ft)
    (fun ft _ => Type_ok.mk_Type_ok _ (ModuleTranslation.funcType_valid ft))
  have himports := forall₂_map env.imports.val
    (fun e => importDecl env.types.val (ModuleEnv.rawImport e))
    (fun e => importType env.types.val e.desc) (Import_ok (importContext env))
    (fun e he => import_typed hc hv he (hiNames e he).1 (hiNames e he).2 _ (importContext_wf env))
  have hglobals := forall₂_map env.globals.val ModuleConstants.global
    (fun g => Translate.globalType g.gtype) (Global_ok C')
    (fun g hg => ModuleConstants.global_typed env g (hv.globals g hg) C' hwC' rfl rfl)
  have htables := forall₂_map tables table EnvTranslation.tableType (Table_ok C')
    (fun tt ht => table_typed hc hv tt ht C' hwC')
  have hmemories := forall₂_map memories memory EnvTranslation.memType (Mem_ok C')
    (fun mt ht => memory_typed hc hv mt ht C' hwC')
  have helements := forall₂_map env.elements.val (fun e => element (ModuleEnv.rawElement e))
    (fun e => Translate.referenceType e.elem) (Elem_ok C') (fun e he => element_typed hv e he)
  have hdatas : Forall (Data_ok C') (segments.map (fun d => ModuleData.translate (ModuleData.raw d))) := by
    simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact (hsegments d hd).typed hv.memoryCount C' hwC' rfl rfl rfl
  have hfuncs := functions_typed hcodes C hmatch hsegmentContext
  have hstart : Forall (Start_ok C) ((env.start.map start).toList) := by
    cases hs : env.start with
    | none => simp [Forall]
    | some idx => simpa [hs, Forall] using start_typed hv idx hs C hmatch
  have hexports := exports_typed hxts heNames C hmatch
  have hmodule : wf_module (moduleOf (fromEnv env tables memories codes segments)) := by
    constructor
    · simpa [fromEnv, List.map_map, Function.comp_def] using forall₂_left himports wf_import (fun _ _ h => Import_ok.wf h)
    · exact forall₂_right hfuncs wf_func (fun _ _ h => Func_ok.wf h)
    · exact forall₂_left hglobals wf_global (fun _ _ h => Global_ok.wf h)
    · exact forall₂_left htables wf_table (fun _ _ h => Table_ok.wf h)
    · exact forall₂_left hmemories wf_mem (fun _ _ h => Mem_ok.wf h)
    · simpa [fromEnv, List.map_map, Function.comp_def] using forall₂_left helements wf_elem (fun _ _ h => Elem_ok.wf h)
    · simpa [fromEnv, List.map_map, Function.comp_def] using (show Forall wf_data (segments.map (fun d => ModuleData.translate (ModuleData.raw d))) from fun d hd => Data_ok.wf (hdatas d hd))
    · exact fun s hs => Start_ok.wf (hstart s hs)
    · simpa [fromEnv, List.map_map, Function.comp_def] using forall₂_left hexports wf_export (fun _ _ h => Export_ok.wf h)
  unfold moduleOf fromEnv
  apply Module_ok.mk_Module_ok
    (ft'_lst := env.types.val.map EnvTranslation.funcType)
    (ixt_lst := importTypes env) (C' := C')
    (gt_lst := env.globals.val.map (fun g => Translate.globalType g.gtype))
    (tt_lst := tables.map EnvTranslation.tableType) (mt_lst := memories.map EnvTranslation.memType)
    (rt_lst := EnvTranslation.elementTypes env) (C := C)
    (ft_lst := env.func_type_indices.val.map (functionType env.types.val))
    (xt_lst := xts.map ModuleExternals.externalType)
    (ift_lst := ModuleTranslation.funcs (importTypes env))
    (igt_lst := ModuleTranslation.globals (importTypes env))
    (itt_lst := ModuleTranslation.tables (importTypes env))
    (imt_lst := ModuleTranslation.mems (importTypes env))
    (var_0 := ModuleTranslation.funcs (importTypes env))
    (var_1 := ModuleTranslation.globals (importTypes env))
    (var_2 := ModuleTranslation.tables (importTypes env))
    (var_3 := ModuleTranslation.mems (importTypes env)) (v_n := segments.length)
  · exact ModuleTranslation.mems_spec _
  · exact ModuleTranslation.tables_spec _
  · exact ModuleTranslation.globals_spec _
  · exact ModuleTranslation.funcs_spec _
  · exact htypes.length_eq
  · exact forall₂_generated htypes
  · simp [importTypes]
  · simpa [importContext, importTypes, List.map_map, Function.comp_def] using forall₂_generated himports
  · exact hglobals.length_eq
  · exact forall₂_generated hglobals
  · exact htables.length_eq
  · exact forall₂_generated htables
  · exact hmemories.length_eq
  · exact forall₂_generated hmemories
  · simp [EnvTranslation.elementTypes]
  · simpa [List.map_map, Function.comp_def, EnvTranslation.elementTypes] using forall₂_generated helements
  · simpa [List.map_map, Function.comp_def] using hdatas
  · exact hfuncs.length_eq
  · exact forall₂_generated hfuncs
  · exact hstart
  · simpa using hxts.length_eq
  · simpa [List.map_map, Function.comp_def] using forall₂_generated hexports
  · have h := hv.memoryCount; rw [hc.memories, List.length_append] at h; simpa using (show memories.length ≤ 1 by omega)
  · simpa [C, List.map_const'] using moduleContext_eq hc (EnvTranslation.elementTypes env) segments.length
  · exact initializerContext_eq hc
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [importTypes, Forall, List.mem_map]
    rintro _ ⟨e, _, rfl⟩
    exact importType_wf _ _
  · exact hwC'
  · exact hwC
  · exact forall₂_right hexports wf_externtype (fun _ _ h => Export_ok.type_wf h)
  · rw [importTypes, tables_imports]
    simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact EnvTranslation.tableType_wf tt
  · rw [importTypes, mems_imports]
    simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact EnvTranslation.memType_wf mt
  · exact hmodule
  · exact importContext_wf env
  · simpa [C, List.map_const', moduleContext_eq hc] using hwC
  · rw [← initializerContext_eq hc]
    exact hwC'
  · simp

end Itasca.ModuleElaboration

end

/-! ## Declared -/

section

/-!
# Declared references of the elaborated module

Connects the environment's `declared_funcs` cache to `DeclaredReferences.declarations`, the
function references declared by the elaborated module. `collected_declared` shows every cached
declaration is syntactically declared, and `coherent_declared_iff` shows the cache and the
declarations have the same members once elements and segments are valid.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleReferences

open ModuleElaboration

/-- A global's declared indices agree with the SpecTec collector. -/
theorem global_indices (entry : metadata.Global) :
    DeclaredReferences.globalIndices (ModuleConstants.global entry) =
      (global entry).map (fun index => uN.mk_uN index.val) :=
  initializer_indices entry.init

/-- An export's declared indices agree with the SpecTec collector. -/
theorem export_indices (entry : metadata.Export) :
    DeclaredReferences.exportIndices (exportDecl (ModuleEnv.rawExport entry)) =
      (exportIndices entry).map (fun index => uN.mk_uN index.val) := by
  cases h : entry.desc <;>
    simp [DeclaredReferences.exportIndices, exportDecl, exportIndex,
      ModuleEnv.rawExport, exportIndices, h]

/-- An element initializer's declared index is found by the SpecTec collector. -/
theorem element_member {entry : metadata.Element} {idx : U32} (h : idx ∈ element entry) :
    uN.mk_uN idx.val ∈ DeclaredReferences.elementIndices
      (ModuleElaboration.element (ModuleEnv.rawElement entry)) := by
  obtain ⟨init, hi, hidx⟩ := List.mem_flatMap.mp h
  simp only [ModuleElaboration.element, ModuleEnv.rawElement, DeclaredReferences.elementIndices]
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨ModuleConstants.expression init, List.mem_map.mpr ⟨init, hi, rfl⟩, ?_⟩
  rw [initializer_indices]
  exact List.mem_map.mpr ⟨idx, hidx, rfl⟩

/-- A valid `i32` constant expression declares no function. -/
theorem valid_i32_initializer {env init} (h : ModuleConstants.Valid env init .I32) :
    initializer init = [] := by
  generalize ht : wasm_types.ValueType.I32 = ty at h
  cases h <;> try rfl
  cases ht

/-- For a valid element segment, the SpecTec collector finds exactly the declared indices of its
initializers. -/
theorem element_indices {env entry} (h : ModuleSegments.elementValid env entry) :
    DeclaredReferences.elementIndices (ModuleElaboration.element (ModuleEnv.rawElement entry)) =
      (element entry).map (fun index => uN.mk_uN index.val) := by
  have hoffset : DeclaredReferences.elementModeIndices (ModuleSegments.elementMode entry.mode) = [] := by
    cases hm : entry.mode with
    | Passive => rfl
    | Declarative => rfl
    | Active index offset =>
      obtain ⟨hi, ht, ho⟩ := (show ∃ hi : index.val < env.table_types.val.length,
        env.table_types.val[index.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32 from by simpa [hm] using h.1)
      simp [ModuleSegments.elementMode, DeclaredReferences.elementModeIndices,
        initializer_indices, valid_i32_initializer ho]
  simp [ModuleElaboration.element, ModuleEnv.rawElement, DeclaredReferences.elementIndices,
    hoffset, List.flatMap_map, initializer_indices, element, List.map_flatMap]

/-- A valid data segment declares no function. -/
theorem data_indices {env entry} (h : ModuleData.Valid env entry) :
    DeclaredReferences.dataIndices (ModuleData.translate (ModuleData.raw entry)) = [] := by
  cases hm : entry.mode with
  | Passive => simp [ModuleData.translate, ModuleData.raw, hm, ModuleSegments.dataMode, DeclaredReferences.dataIndices]
  | Active index offset =>
    obtain ⟨hi, ho⟩ := (show index.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32 from by simpa [ModuleData.Valid, hm] using h)
    simp [ModuleData.translate, ModuleData.raw, hm, ModuleSegments.dataMode,
      DeclaredReferences.dataIndices, initializer_indices, valid_i32_initializer ho]

/-- Every function index collected by the environment is declared in the elaborated module.
Offset declarations can only enlarge the declared set, so this implication needs no typing
premise. -/
theorem collected_declared {env : metadata.Env} {tables memories codes segments}
    {idx : U32} (h : idx ∈ collected env) :
    uN.mk_uN idx.val ∈ DeclaredReferences.declarations
      (moduleOf (fromEnv env tables memories codes segments)) := by
  simp only [collected, List.mem_append] at h
  simp only [DeclaredReferences.declarations, moduleOf, fromEnv,
    List.flatMap_map, List.mem_append, List.mem_flatMap]
  rcases h with (hg | he) | hel
  · obtain ⟨entry, hm, hi⟩ := List.mem_flatMap.mp hg
    apply Or.inl
    apply Or.inl
    apply Or.inl
    refine ⟨entry, hm, ?_⟩
    rw [global_indices]
    exact List.mem_map.mpr ⟨idx, hi, rfl⟩
  · obtain ⟨entry, hm, hi⟩ := List.mem_flatMap.mp he
    apply Or.inr
    refine ⟨entry, hm, ?_⟩
    rw [export_indices]
    exact List.mem_map.mpr ⟨idx, hi, rfl⟩
  · obtain ⟨entry, hm, hi⟩ := List.mem_flatMap.mp hel
    exact Or.inl (Or.inl (Or.inr ⟨entry, hm, element_member hi⟩))

/-- Every index in a coherent `declared_funcs` cache is declared in the elaborated module. -/
theorem coherent_declared {env : metadata.Env} {tables memories codes segments}
    (h : Coherent env) :
    ∀ index ∈ env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val),
      index ∈ DeclaredReferences.declarations
        (moduleOf (fromEnv env tables memories codes segments)) := by
  intro index hm
  obtain ⟨idx, hi, rfl⟩ := List.mem_map.mp hm
  rw [h] at hi
  exact collected_declared hi

/-- Typing forces every segment offset to be an `i32` constant expression, so all syntactic
function declarations are in the `declared_funcs` cache, and the cache and the declarations have
the same members. -/
theorem coherent_declared_iff {env : metadata.Env} {tables memories codes segments}
    (hc : Coherent env) (he : ∀ entry ∈ env.elements.val, ModuleSegments.elementValid env entry)
    (hd : ∀ entry ∈ segments, ModuleData.Valid env entry) (index : funcidx) :
    index ∈ env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val) ↔
      index ∈ DeclaredReferences.declarations (moduleOf (fromEnv env tables memories codes segments)) := by
  have helem : env.elements.val.flatMap (fun e =>
      DeclaredReferences.elementIndices (ModuleElaboration.element (ModuleEnv.rawElement e))) =
      env.elements.val.flatMap (fun e => (element e).map (fun idx => uN.mk_uN idx.val)) := by
    apply List.flatMap_congr
    intro e hm
    exact element_indices (he e hm)
  have hdata : segments.flatMap (fun d => DeclaredReferences.dataIndices (ModuleData.translate (ModuleData.raw d))) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro d hm
    exact data_indices (hd d hm)
  change env.declared_funcs.val = collected env at hc
  rw [hc]
  simp only [collected, List.map_append, List.map_flatMap,
    DeclaredReferences.declarations, moduleOf, fromEnv, List.flatMap_map,
    global_indices, export_indices, helem, hdata, List.append_nil,
    List.mem_append]
  tauto

end Itasca.ModuleReferences

end

/-! ## Profile -/

section

/-!
# Module-level restrictions

`Restrictions` collects the explicit conditions on a raw module that the
generated 2.0 judgment does not express: `ModuleConditions` and declared function references. The theorem `restrictions`
derives it for a valid cached environment with typed code entries, and `elaborates` shows such a
module elaborates with in-bounds type references.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The explicit restrictions that supplement the generated 2.0 judgment. Neither
these conditions nor elaboration mention validator calls. -/
structure Restrictions (raw : ModuleBinary.Module) : Prop
    extends ModuleConditions raw where
  declared : DeclaredReferences.Module (moduleOf raw)

/-- Distinct export byte names in a valid environment have distinct decoded names. -/
theorem export_names_distinct {env : metadata.Env} (hv : ModuleEnv.Valid env) :
    (env.exports.val.map (fun e => ModuleBinary.nameOfBytes e.name.val)).Nodup := by
  have h := hv.distinctExports.map_on (f := ModuleBinary.nameOfBytes) ?_
  · simpa [List.map_map, Function.comp_def] using h
  · intro x hx y hy he
    obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ey, hey, rfl⟩ := List.mem_map.mp hy
    exact (hv.exportNames ex hex).nameOfBytes_injective (hv.exportNames ey hey) he

/-- A valid cached environment with typed code entries gives the module-level `Restrictions` of the
module it describes. -/
theorem restrictions {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes) :
    Restrictions (fromEnv env tables memories codes segments) := by
  constructor
  · constructor
    · simpa [fromEnv, ModuleEnv.rawExport, List.map_map, Function.comp_def] using export_names_distinct hv
    · have h := hv.memoryCount
      rw [hc.memories, List.length_append] at h
      simpa [fromEnv, ModuleEnv.rawImport, List.map_map, Function.comp_def, mems_imports] using h
  · change ∀ f ∈ List.zipWith CodeEntry.function env.func_type_indices.val codes,
      DeclaredReferences.Function _ f
    have hall : ∀ f ∈ List.zipWith CodeEntry.function env.func_type_indices.val codes,
        DeclaredReferences.Function
          (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) f := by
      generalize hi : env.func_type_indices.val = indices at hcodes ⊢
      clear hi
      induction hcodes with
      | nil => simp
      | cons hp htail ih =>
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hp.declared
        · exact ih f hf
    intro f hf
    exact (hall f hf).mono (ModuleReferences.coherent_declared hv.references)

/-- A cached environment with typed code entries elaborates its module with in-bounds type
references and matching code counts. -/
theorem elaborates {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes) :
    Elaborates (fromEnv env tables memories codes segments)
      (moduleOf (fromEnv env tables memories codes segments)) := by
  constructor
  · rfl
  · intro entry he idx hidx
    change entry ∈ env.imports.val.map ModuleEnv.rawImport at he
    obtain ⟨e, hmem, heq⟩ := (List.mem_map.mp he : ∃ e ∈ env.imports.val, ModuleEnv.rawImport e = entry)
    subst entry
    apply hc.import_indices idx
    simp only [ModuleEnv.importedFuncs, List.mem_filterMap]
    exact ⟨e, hmem, by simp [ModuleEnv.rawImport] at hidx; simp [hidx]⟩
  · intro idx hi
    change idx ∈ env.func_type_indices.val at hi
    change idx.val < env.types.val.length
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hi
    have hc' := hcodes.get hj (by rw [← hcodes.length_eq]; exact hj)
    simpa [List.get_eq_getElem, he] using hc'.type_lt
  · exact hcodes.length_eq

end Itasca.ModuleElaboration

end
