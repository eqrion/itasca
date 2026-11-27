import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Env.Encoding
import Itasca.Binary.ModuleUnique
import Itasca.Module.Code.ContextTransport
import Itasca.Module.Elab.SegmentTyping
import Itasca.Support.Translation
import Mathlib.Data.List.Nodup

open WebAssembly

/-!
Proofs for Module / Elab.

This module collects ToTyping, FromTyping.
Each section documents its contracts and consumers.
-/

/-! ## ToTyping -/

section

/-!
# Generated typing from validated declarations

Environment caches and section-validity conditions construct generated module typing,
elaboration and metadata correspondence. Declared-reference coherence and distinct export
names remain explicit additional restrictions.
-/

/-! ## Elaboration -/

section

/-!
# Elaboration of raw modules

`moduleOf` translates a raw `Binary.Module` into the SpecTec `module` syntax, expanding the
binary representation's indexed forms. `Elaborates` relates a SpecTec module to a raw one, and
`ModuleConditions` states the module-level restrictions that the generated 2.0 judgment lacks.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- An in-bounds type index looks up its translated function type. -/
theorem function_type_lookup {types : List wasm_types.FuncType} {idx : U32}
    (hi : idx.val < types.length) :
    functionType types idx = Translation.Environment.funcType types[idx.val] := by
  simp [functionType, List.getElem?_eq_getElem hi]

end Itasca.Module.Elaboration

end

/-! ## ExternalTyping -/

section

/-!
# Typing of imports, exports and the start function

Generated typing judgments (`Import_ok`, `Export_ok`, `Externidx_ok`, `Start_ok`) for the imports,
exports and start function of a valid cached environment. `import_typed` and `export_typed` give
the external type that `Module.Externals.ImportResolves` and `ExportResolves` describe.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- The SpecTec translation of an external type is well formed. -/
theorem external_type_wf (xt : wasm_types.ExternType) : wf_externtype (Module.Externals.externalType xt) := by
  cases xt with
  | Func ft => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (Translation.Environment.table_type_wf tt)
  | Memory mt => exact .externtype_case_3 _ (Translation.Environment.mem_type_wf mt)

/-- The SpecTec external index of an export descriptor is well formed. -/
theorem export_index_wf (desc : metadata.ExportDesc) : wf_externidx (exportIndex desc) := by
  cases desc with
  | Func idx => exact .externidx_case_0 _ (Translation.Environment.index_wf idx)
  | Table idx => exact .externidx_case_2 _ (Translation.Environment.index_wf idx)
  | Memory idx => exact .externidx_case_3 _ (Translation.Environment.index_wf idx)
  | Global idx => exact .externidx_case_1 _ (Translation.Environment.index_wf idx)

/-- A resolved import has the translated external type as its `importType`. -/
theorem import_type_resolved {env : metadata.Env} {entry : metadata.Import} {xt : wasm_types.ExternType}
    (h : Module.Externals.ImportResolves env entry xt) :
    importType env.types.val entry.desc = Module.Externals.externalType xt := by
  cases hd : entry.desc with
  | Func idx =>
    simp only [Module.Externals.ImportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    simp [importType, Module.Externals.externalType, function_type_lookup hi]
  | Table tt =>
    simp only [Module.Externals.ImportResolves, hd] at h
    simp [h, importType, Module.Externals.externalType]
  | Memory mt =>
    simp only [Module.Externals.ImportResolves, hd] at h
    simp [h, importType, Module.Externals.externalType]
  | Global gt =>
    simp only [Module.Externals.ImportResolves, hd] at h
    simp [h, importType, Module.Externals.externalType]

/-- A resolved export index has the translated external type in the module context. -/
theorem export_index_typed {env : metadata.Env} {entry : metadata.Export} {xt : wasm_types.ExternType}
    (h : Module.Externals.ExportResolves env entry xt)
    (C : context) (hC : CodeEntry.ModuleContext env C) :
    Externidx_ok C (exportIndex entry.desc) (Module.Externals.externalType xt) := by
  cases hd : entry.desc with
  | Func idx =>
    simp only [Module.Externals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.func C _ _
    · simpa [hC.funcs, proj_uN_0] using hi
    · simp only [hC.funcs, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using export_index_wf entry.desc
    · exact .externtype_case_0 _
  | Table idx =>
    simp only [Module.Externals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.table C _ _
    · simpa [hC.tables, proj_uN_0] using hi
    · simp only [hC.tables, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using export_index_wf entry.desc
    · exact .externtype_case_2 _ (Translation.Environment.table_type_wf _)
  | Memory idx =>
    simp only [Module.Externals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.mem C _ _
    · simpa [hC.mems, proj_uN_0] using hi
    · simp only [hC.mems, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using export_index_wf entry.desc
    · exact .externtype_case_3 _ (Translation.Environment.mem_type_wf _)
  | Global idx =>
    simp only [Module.Externals.ExportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    apply Externidx_ok.global C _ _
    · simpa [hC.globals, proj_uN_0] using hi
    · simp only [hC.globals, proj_uN_0]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    · exact hC.wf
    · simpa [hd, exportIndex] using export_index_wf entry.desc
    · exact .externtype_case_1 _

/-- A resolved export with a well-formed name is typed in the module context. -/
theorem export_typed {env : metadata.Env} {entry : metadata.Export} {xt : wasm_types.ExternType}
    (h : Module.Externals.ExportResolves env entry xt)
    (hn : wf_name (Binary.nameOfBytes entry.name.val))
    (C : context) (hC : CodeEntry.ModuleContext env C) :
    Export_ok C (exportDecl (Module.Environment.rawExport entry)) (Module.Externals.externalType xt) := by
  exact .mk_Export_ok C _ _ _ (export_index_typed h C hC) hC.wf (external_type_wf xt)
    (.export_case_0 _ _ hn (export_index_wf entry.desc))

/-- `functionType` always gives a valid function type. -/
theorem function_type_valid (types : List wasm_types.FuncType) (idx : U32) :
    Functype_ok (functionType types idx) := by
  cases he : types[idx.val]? with
  | none => simp only [functionType, he, Option.map_none, Option.getD_none]; constructor
  | some ft => simpa [functionType, he] using Module.Translation.func_type_valid ft

/-- An import's SpecTec external type is well formed. -/
theorem import_type_wf (types : List wasm_types.FuncType) (desc : metadata.ImportDesc) :
    wf_externtype (importType types desc) := by
  cases desc with
  | Func idx => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (Translation.Environment.table_type_wf tt)
  | Memory mt => exact .externtype_case_3 _ (Translation.Environment.mem_type_wf mt)

/-- The external type of each import of a valid cached environment is valid. -/
theorem import_type_valid {env : metadata.Env} {tables memories entry}
    (hc : Module.Environment.Cache env tables memories) (hv : Module.Environment.Valid env)
    (he : entry ∈ env.imports.val) : Externtype_ok (importType env.types.val entry.desc) := by
  cases hd : entry.desc with
  | Func idx => exact .func _ (function_type_valid _ _) (.externtype_case_0 _)
  | Global gt => exact .global _ (Translation.global_type_valid gt) (.externtype_case_1 _)
  | Table tt =>
    have hi : tt ∈ Module.Environment.importedTables env.imports.val := by
      simp only [Module.Environment.importedTables, List.mem_filterMap]
      exact ⟨entry, he, by simp [hd]⟩
    have ht : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_left _ hi
    exact .table _ (Module.Translation.table_type_valid tt (hv.tables tt ht))
      (.externtype_case_2 _ (Translation.Environment.table_type_wf tt))
  | Memory mt =>
    have hi : mt ∈ Module.Environment.importedMems env.imports.val := by
      simp only [Module.Environment.importedMems, List.mem_filterMap]
      exact ⟨entry, he, by simp [hd]⟩
    have ht : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_left _ hi
    exact .mem _ (Module.Translation.mem_type_valid mt (hv.memories mt ht))
      (.externtype_case_3 _ (Translation.Environment.mem_type_wf mt))

/-- Each import of a valid cached environment is typed, given well-formed names. -/
theorem import_typed {env : metadata.Env} {tables memories entry}
    (hc : Module.Environment.Cache env tables memories) (hv : Module.Environment.Valid env)
    (he : entry ∈ env.imports.val)
    (hmod : wf_name (Binary.nameOfBytes entry.module.val))
    (hn : wf_name (Binary.nameOfBytes entry.name.val))
    (C : context) (hC : wf_context C) :
    Import_ok C (importDecl env.types.val (Module.Environment.rawImport entry))
      (importType env.types.val entry.desc) := by
  exact .mk_Import_ok C _ _ _ (import_type_valid hc hv he) hC
    (.import_case_0 _ _ _ hmod hn (import_type_wf _ _))

/-- The start function of a valid environment is typed in the module context. -/
theorem start_typed {env : metadata.Env} (hv : Module.Environment.Valid env) (idx : U32)
    (hs : env.start = some idx) (C : context) (hC : CodeEntry.ModuleContext env C) :
    Start_ok C (start idx) := by
  obtain ⟨hi, hp, hr⟩ := hv.start idx hs
  apply Start_ok.mk_Start_ok C _
  · simpa [hC.funcs, proj_uN_0] using hi
  · simp only [hC.funcs, proj_uN_0]
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map]
    simp [Translation.Environment.funcType, hp, hr]
  · exact hC.wf
  · exact .start_case_0 _ (Translation.Environment.index_wf idx)

end Itasca.Module.Elaboration

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

namespace Itasca.Module.Elaboration

/-- The SpecTec external types of the environment's imports, in order. -/
def importTypes (env : metadata.Env) : List externtype :=
  env.imports.val.map (fun entry => importType env.types.val entry.desc)

/-- The function space translated from import types is the translation of `importedFuncs`. -/
theorem funcs_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    Module.Translation.funcs (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedFuncs entries).map (functionType types) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedFuncs, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.funcs, importType, Module.Environment.importedFuncs, hd, ih]

/-- The global space translated from import types is the translation of `importedGlobals`. -/
theorem globals_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    Module.Translation.globals (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedGlobals entries).map Translation.globalType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedGlobals, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.globals, importType, Module.Environment.importedGlobals, hd, ih]

/-- The table space translated from import types is the translation of `importedTables`. -/
theorem tables_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    Module.Translation.tables (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedTables entries).map Translation.Environment.tableType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedTables, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.tables, importType, Module.Environment.importedTables, hd, ih]

/-- The memory space translated from import types is the translation of `importedMems`. -/
theorem mems_imports (types : List wasm_types.FuncType) (entries : List metadata.Import) :
    Module.Translation.mems (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedMems entries).map Translation.Environment.memType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedMems, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.mems, importType, Module.Environment.importedMems, hd, ih]

/-- Resolved type indices translate to the translated function types. -/
theorem resolved_functions {types indices fts}
    (h : List.Forall₂ (Module.Environment.Resolves types) indices fts) :
    indices.map (functionType types) = fts.map Translation.Environment.funcType := by
  induction h with
  | nil => rfl
  | cons hf _ ih =>
    obtain ⟨hi, he⟩ := hf
    simp [function_type_lookup hi, he, ih]

/-- The translated function cache is the imported functions followed by the defined ones. -/
theorem funcs_cache {env tables memories} (h : Module.Environment.Cache env tables memories) :
    env.func_types.val.map Translation.Environment.funcType = Module.Translation.funcs (importTypes env) ++
      env.func_type_indices.val.map (functionType env.types.val) := by
  rw [importTypes, funcs_imports]
  simpa using (resolved_functions h.funcs).symm

/-- The translated global cache is the imported globals followed by the defined ones. -/
theorem globals_cache {env tables memories} (h : Module.Environment.Cache env tables memories) :
    env.global_types.val.map Translation.globalType = Module.Translation.globals (importTypes env) ++
      env.globals.val.map (fun g => Translation.globalType g.gtype) := by
  simp [importTypes, globals_imports, h.globals, List.map_append, List.map_map]

/-- The translated table cache is the imported tables followed by the defined ones. -/
theorem tables_cache {env tables memories} (h : Module.Environment.Cache env tables memories) :
    env.table_types.val.map Translation.Environment.tableType = Module.Translation.tables (importTypes env) ++
      tables.map Translation.Environment.tableType := by
  simp [importTypes, tables_imports, h.tables, List.map_append]

/-- The translated memory cache is the imported memories followed by the defined ones. -/
theorem memories_cache {env tables memories} (h : Module.Environment.Cache env tables memories) :
    env.mem_types.val.map Translation.Environment.memType = Module.Translation.mems (importTypes env) ++
      memories.map Translation.Environment.memType := by
  simp [importTypes, mems_imports, h.memories, List.map_append]

/-- The typing context for functions, elements, segments and exports: the environment's translated
index spaces, the given element types and `dataCount` data segments, and no locals or labels. -/
def moduleContext (env : metadata.Env) (elementTypes : List elemtype) (dataCount : Nat) : context :=
  { TYPES := env.types.val.map Translation.Environment.funcType
    FUNCS := env.func_types.val.map Translation.Environment.funcType
    GLOBALS := env.global_types.val.map Translation.globalType
    TABLES := env.table_types.val.map Translation.Environment.tableType
    MEMS := env.mem_types.val.map Translation.Environment.memType
    ELEMS := elementTypes
    DATAS := List.replicate dataCount datatype.OK
    LOCALS := []
    LABELS := []
    RETURN := none }

/-- The typing context for constant initializers: `moduleContext` with no segment spaces and only
the imported globals. -/
def initializerContext (env : metadata.Env) : context :=
  { moduleContext env [] 0 with
    GLOBALS := (env.global_types.val.take env.num_imported_globals.val).map Translation.globalType }

/-- `moduleContext` is a `CodeEntry.ModuleContext` for the environment. -/
theorem module_context_matches (env : metadata.Env) (elementTypes : List elemtype) (dataCount : Nat) :
    CodeEntry.ModuleContext env (moduleContext env elementTypes dataCount) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `moduleContext` is well formed. -/
theorem module_context_wf (env : metadata.Env) (elementTypes : List elemtype) (dataCount : Nat) :
    wf_context (moduleContext env elementTypes dataCount) :=
  (module_context_matches env elementTypes dataCount).wf

/-- `initializerContext` is well formed. -/
theorem initializer_context_wf (env : metadata.Env) : wf_context (initializerContext env) := by
  cases module_context_wf env [] 0
  constructor <;> assumption

end Itasca.Module.Elaboration

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

namespace Itasca.Module.Elaboration

/-- Each element segment of a valid environment is typed in the initializer context. -/
theorem element_typed {env : metadata.Env} (hv : Module.Environment.Valid env)
    (entry : metadata.Element) (he : entry ∈ env.elements.val) :
    Elem_ok (initializerContext env) (element (Module.Environment.rawElement entry))
      (Translation.referenceType entry.elem) := by
  exact (hv.elements entry he).typed (initializerContext env) (initializer_context_wf env)
    rfl rfl rfl

/-- Each defined table of a valid cached environment is typed in any well-formed context. -/
theorem table_typed {env tables memories} (hc : Module.Environment.Cache env tables memories)
     (hv : Module.Environment.Valid env) (tt : wasm_types.TableType) (ht : tt ∈ tables)
    (C : context) (hC : wf_context C) :
    Table_ok C (table tt) (Translation.Environment.tableType tt) := by
  have hm : tt ∈ env.table_types.val := by rw [hc.tables]; exact List.mem_append_right _ ht
  exact .mk_Table_ok C _ (Module.Translation.table_type_valid tt (hv.tables tt hm)) hC
    (.table_case_0 _ (Translation.Environment.table_type_wf tt))

/-- Each defined memory of a valid cached environment is typed in any well-formed context. -/
theorem memory_typed {env tables memories} (hc : Module.Environment.Cache env tables memories)
     (hv : Module.Environment.Valid env) (mt : wasm_types.MemType) (ht : mt ∈ memories)
    (C : context) (hC : wf_context C) :
    Mem_ok C (memory mt) (Translation.Environment.memType mt) := by
  have hm : mt ∈ env.mem_types.val := by rw [hc.memories]; exact List.mem_append_right _ ht
  exact .mk_Mem_ok C _ (Module.Translation.mem_type_valid mt (hv.memories mt hm)) hC
    (.mem_case_0 _ (Translation.Environment.mem_type_wf mt))

end Itasca.Module.Elaboration

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

namespace Itasca.Module.Elaboration

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
    simpa [function_type_lookup hp.type_lt] using hp.func_ok C hc hsegments

/-- Resolved exports with well-formed names are typed in a module context. -/
theorem exports_typed {env entries xts}
    (h : List.Forall₂ (Module.Externals.ExportResolves env) entries xts)
    (hn : ∀ entry ∈ entries, wf_name (Binary.nameOfBytes entry.name.val))
    (C : context) (hc : CodeEntry.ModuleContext env C) :
    List.Forall₂ (Export_ok C) (entries.map (fun e => exportDecl (Module.Environment.rawExport e)))
      (xts.map Module.Externals.externalType) := by
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

end Itasca.Module.Elaboration

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

namespace Itasca.Module.Elaboration

/-- If the environment represents the declarations, the declarations' raw module is `fromEnv`. -/
theorem represents_module {env decls codes segments} (h : Module.Environment.Represents env decls) :
    decls.module codes (segments.map Module.Data.raw) =
      fromEnv env decls.tables decls.memories codes segments := by
  simp [Module.Environment.Declarations.module, fromEnv, h.types, h.imports, h.functions,
    h.globals, h.exports, h.start, h.elements, h.dataCount]

/-- The context for import typing: only the module's types. -/
def importContext (env : metadata.Env) : context :=
  ⟨env.types.val.map Translation.Environment.funcType, [], [], [], [], [], [], [], [], none⟩

/-- The import context is well formed. -/
theorem import_context_wf (env : metadata.Env) : wf_context (importContext env) := by
  constructor <;> simp [Forall]

/-- For a cached environment, `moduleContext` is the imported spaces followed by the defined
spaces, with the given element spaces and data count. -/
theorem module_context_eq {env tables memories} (hc : Module.Environment.Cache env tables memories)
    (es : List elemtype) (nd : Nat) :
    moduleContext env es nd =
      ⟨env.types.val.map Translation.Environment.funcType,
        Module.Translation.funcs (importTypes env) ++ env.func_type_indices.val.map (functionType env.types.val),
        Module.Translation.globals (importTypes env) ++ env.globals.val.map (fun g => Translation.globalType g.gtype),
        Module.Translation.tables (importTypes env) ++ tables.map Translation.Environment.tableType,
        Module.Translation.mems (importTypes env) ++ memories.map Translation.Environment.memType,
        es, List.replicate nd .OK, [], [], none⟩ := by
  simp only [moduleContext, funcs_cache hc, globals_cache hc, tables_cache hc, memories_cache hc]

/-- For a cached environment, `initializerContext` has the imported globals only and no local,
label or segment spaces. -/
theorem initializer_context_eq {env tables memories} (hc : Module.Environment.Cache env tables memories) :
    initializerContext env =
      ⟨env.types.val.map Translation.Environment.funcType,
        Module.Translation.funcs (importTypes env) ++ env.func_type_indices.val.map (functionType env.types.val),
        Module.Translation.globals (importTypes env),
        Module.Translation.tables (importTypes env) ++ tables.map Translation.Environment.tableType,
        Module.Translation.mems (importTypes env) ++ memories.map Translation.Environment.memType,
        [], [], [], [], none⟩ := by
  simp only [initializerContext, moduleContext, funcs_cache hc, tables_cache hc,
    memories_cache hc, hc.global_prefix, importTypes, globals_imports, List.replicate_zero]

/-- A valid cached environment with typed code entries, valid data segments and resolved exports
has `Module_ok` for its elaborated module. All section judgments are assembled in one coherent
module context, and name well-formedness comes from the independent byte grammar. -/
theorem typed {env : metadata.Env} {tables memories codes segments xts}
    (hc : Module.Environment.Cache env tables memories) (hv : Module.Environment.Valid env)
    (hiNames : ∀ entry ∈ env.imports.val,
      wf_name (Binary.nameOfBytes entry.module.val) ∧ wf_name (Binary.nameOfBytes entry.name.val))
    (heNames : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val))
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (hsegments : ∀ segment ∈ segments, Module.Data.Valid env segment)
    (hdataCount : ∀ count, env.data_count = some count → count.val = segments.length)
    (hxts : List.Forall₂ (Module.Externals.ExportResolves env) env.exports.val xts) :
    Module_ok (moduleOf (fromEnv env tables memories codes segments)) := by
  let C := moduleContext env (Translation.Environment.elementTypes env) segments.length
  let C' := initializerContext env
  have hwC := module_context_wf env (Translation.Environment.elementTypes env) segments.length
  have hwC' := initializer_context_wf env
  have hmatch := module_context_matches env (Translation.Environment.elementTypes env) segments.length
  have hsegmentContext : CodeEntry.SegmentContext env C := by
    constructor
    · simp [C, moduleContext]
    · cases hd : env.data_count with
      | none => simp [C, moduleContext, Translation.Environment.dataTypes, hd]
      | some count => simp [C, moduleContext, Translation.Environment.dataTypes, hd, hdataCount count hd]
  have htypes := forall₂_map env.types.val Translation.Environment.funcType
    (fun ft => type.TYPE (Translation.Environment.funcType ft)) (fun ft ty => Type_ok ty ft)
    (fun ft _ => Type_ok.mk_Type_ok _ (Module.Translation.func_type_valid ft))
  have himports := forall₂_map env.imports.val
    (fun e => importDecl env.types.val (Module.Environment.rawImport e))
    (fun e => importType env.types.val e.desc) (Import_ok (importContext env))
    (fun e he => import_typed hc hv he (hiNames e he).1 (hiNames e he).2 _ (import_context_wf env))
  have hglobals := forall₂_map env.globals.val Module.Constants.global
    (fun g => Translation.globalType g.gtype) (Global_ok C')
    (fun g hg => Module.Constants.global_typed env g (hv.globals g hg) C' hwC' rfl rfl)
  have htables := forall₂_map tables table Translation.Environment.tableType (Table_ok C')
    (fun tt ht => table_typed hc hv tt ht C' hwC')
  have hmemories := forall₂_map memories memory Translation.Environment.memType (Mem_ok C')
    (fun mt ht => memory_typed hc hv mt ht C' hwC')
  have helements := forall₂_map env.elements.val (fun e => element (Module.Environment.rawElement e))
    (fun e => Translation.referenceType e.elem) (Elem_ok C') (fun e he => element_typed hv e he)
  have hdatas : Forall (Data_ok C') (segments.map (fun d => Module.Data.translate (Module.Data.raw d))) := by
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
    · simpa [fromEnv, List.map_map, Function.comp_def] using (show Forall wf_data (segments.map (fun d => Module.Data.translate (Module.Data.raw d))) from fun d hd => Data_ok.wf (hdatas d hd))
    · exact fun s hs => Start_ok.wf (hstart s hs)
    · simpa [fromEnv, List.map_map, Function.comp_def] using forall₂_left hexports wf_export (fun _ _ h => Export_ok.wf h)
  unfold moduleOf fromEnv
  apply Module_ok.mk_Module_ok
    (ft'_lst := env.types.val.map Translation.Environment.funcType)
    (ixt_lst := importTypes env) (C' := C')
    (gt_lst := env.globals.val.map (fun g => Translation.globalType g.gtype))
    (tt_lst := tables.map Translation.Environment.tableType) (mt_lst := memories.map Translation.Environment.memType)
    (rt_lst := Translation.Environment.elementTypes env) (C := C)
    (ft_lst := env.func_type_indices.val.map (functionType env.types.val))
    (xt_lst := xts.map Module.Externals.externalType)
    (ift_lst := Module.Translation.funcs (importTypes env))
    (igt_lst := Module.Translation.globals (importTypes env))
    (itt_lst := Module.Translation.tables (importTypes env))
    (imt_lst := Module.Translation.mems (importTypes env))
    (var_0 := Module.Translation.funcs (importTypes env))
    (var_1 := Module.Translation.globals (importTypes env))
    (var_2 := Module.Translation.tables (importTypes env))
    (var_3 := Module.Translation.mems (importTypes env)) (v_n := segments.length)
  · exact Module.Translation.mems_spec _
  · exact Module.Translation.tables_spec _
  · exact Module.Translation.globals_spec _
  · exact Module.Translation.funcs_spec _
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
  · simp [Translation.Environment.elementTypes]
  · simpa [List.map_map, Function.comp_def, Translation.Environment.elementTypes] using forall₂_generated helements
  · simpa [List.map_map, Function.comp_def] using hdatas
  · exact hfuncs.length_eq
  · exact forall₂_generated hfuncs
  · exact hstart
  · simpa using hxts.length_eq
  · simpa [List.map_map, Function.comp_def] using forall₂_generated hexports
  · have h := hv.memoryCount; rw [hc.memories, List.length_append] at h; simpa using (show memories.length ≤ 1 by omega)
  · simpa [C, List.map_const'] using module_context_eq hc (Translation.Environment.elementTypes env) segments.length
  · exact initializer_context_eq hc
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [importTypes, Forall, List.mem_map]
    rintro _ ⟨e, _, rfl⟩
    exact import_type_wf _ _
  · exact hwC'
  · exact hwC
  · exact forall₂_right hexports wf_externtype (fun _ _ h => Export_ok.type_wf h)
  · rw [importTypes, tables_imports]
    simp only [Forall, List.mem_map]
    rintro _ ⟨tt, _, rfl⟩
    exact Translation.Environment.table_type_wf tt
  · rw [importTypes, mems_imports]
    simp only [Forall, List.mem_map]
    rintro _ ⟨mt, _, rfl⟩
    exact Translation.Environment.mem_type_wf mt
  · exact hmodule
  · exact import_context_wf env
  · simpa [C, List.map_const', module_context_eq hc] using hwC
  · rw [← initializer_context_eq hc]
    exact hwC'
  · simp

end Itasca.Module.Elaboration

end

/-! ## Declared -/

section

/-!
# Declared references of the elaborated module

Connects the environment's `declared_funcs` cache to `Spec.DeclaredReferences.declarations`, the
function references declared by the elaborated module. `collected_declared` shows every cached
declaration is syntactically declared, and `coherent_declared_iff` shows the cache and the
declarations have the same members once elements and segments are valid.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.References

open Module.Elaboration

/-- A global's declared indices agree with the SpecTec collector. -/
theorem global_indices (entry : metadata.Global) :
    Spec.DeclaredReferences.globalIndices (Module.Constants.global entry) =
      (global entry).map (fun index => uN.mk_uN index.val) :=
  initializer_indices entry.init

/-- An export's declared indices agree with the SpecTec collector. -/
theorem export_indices (entry : metadata.Export) :
    Spec.DeclaredReferences.exportIndices (exportDecl (Module.Environment.rawExport entry)) =
      (exportIndices entry).map (fun index => uN.mk_uN index.val) := by
  cases h : entry.desc <;>
    simp [Spec.DeclaredReferences.exportIndices, exportDecl, exportIndex,
      Module.Environment.rawExport, exportIndices, h]

/-- An element initializer's declared index is found by the SpecTec collector. -/
theorem element_member {entry : metadata.Element} {idx : U32} (h : idx ∈ element entry) :
    uN.mk_uN idx.val ∈ Spec.DeclaredReferences.elementIndices
      (Module.Elaboration.element (Module.Environment.rawElement entry)) := by
  obtain ⟨init, hi, hidx⟩ := List.mem_flatMap.mp h
  simp only [Module.Elaboration.element, Module.Environment.rawElement, Spec.DeclaredReferences.elementIndices]
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨Module.Constants.expression init, List.mem_map.mpr ⟨init, hi, rfl⟩, ?_⟩
  rw [initializer_indices]
  exact List.mem_map.mpr ⟨idx, hidx, rfl⟩

/-- A valid `i32` constant expression declares no function. -/
theorem valid_i32_initializer {env init} (h : Module.Constants.Valid env init .I32) :
    initializer init = [] := by
  generalize ht : wasm_types.ValueType.I32 = ty at h
  cases h <;> try rfl
  cases ht

/-- For a valid element segment, the SpecTec collector finds exactly the declared indices of its
initializers. -/
theorem element_indices {env entry} (h : Module.Segments.elementValid env entry) :
    Spec.DeclaredReferences.elementIndices (Module.Elaboration.element (Module.Environment.rawElement entry)) =
      (element entry).map (fun index => uN.mk_uN index.val) := by
  have hoffset : Spec.DeclaredReferences.elementModeIndices (Module.Segments.elementMode entry.mode) = [] := by
    cases hm : entry.mode with
    | Passive => rfl
    | Declarative => rfl
    | Active index offset =>
      obtain ⟨hi, ht, ho⟩ := (show ∃ hi : index.val < env.table_types.val.length,
        env.table_types.val[index.val].elem = entry.elem ∧ Module.Constants.Valid env offset .I32 from by simpa [hm] using h.1)
      simp [Module.Segments.elementMode, Spec.DeclaredReferences.elementModeIndices,
        initializer_indices, valid_i32_initializer ho]
  simp [Module.Elaboration.element, Module.Environment.rawElement, Spec.DeclaredReferences.elementIndices,
    hoffset, List.flatMap_map, initializer_indices, element, List.map_flatMap]

/-- A valid data segment declares no function. -/
theorem data_indices {env entry} (h : Module.Data.Valid env entry) :
    Spec.DeclaredReferences.dataIndices (Module.Data.translate (Module.Data.raw entry)) = [] := by
  cases hm : entry.mode with
  | Passive => simp [Module.Data.translate, Module.Data.raw, hm, Module.Segments.dataMode, Spec.DeclaredReferences.dataIndices]
  | Active index offset =>
    obtain ⟨hi, ho⟩ := (show index.val < env.mem_types.val.length ∧ Module.Constants.Valid env offset .I32 from by simpa [Module.Data.Valid, hm] using h)
    simp [Module.Data.translate, Module.Data.raw, hm, Module.Segments.dataMode,
      Spec.DeclaredReferences.dataIndices, initializer_indices, valid_i32_initializer ho]

/-- Every function index collected by the environment is declared in the elaborated module.
Offset declarations can only enlarge the declared set, so this implication needs no typing
premise. -/
theorem collected_declared {env : metadata.Env} {tables memories codes segments}
    {idx : U32} (h : idx ∈ collected env) :
    uN.mk_uN idx.val ∈ Spec.DeclaredReferences.declarations
      (moduleOf (fromEnv env tables memories codes segments)) := by
  simp only [collected, List.mem_append] at h
  simp only [Spec.DeclaredReferences.declarations, moduleOf, fromEnv,
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
      index ∈ Spec.DeclaredReferences.declarations
        (moduleOf (fromEnv env tables memories codes segments)) := by
  intro index hm
  obtain ⟨idx, hi, rfl⟩ := List.mem_map.mp hm
  rw [h] at hi
  exact collected_declared hi

/-- Typing forces every segment offset to be an `i32` constant expression, so all syntactic
function declarations are in the `declared_funcs` cache, and the cache and the declarations have
the same members. -/
theorem coherent_declared_iff {env : metadata.Env} {tables memories codes segments}
    (hc : Coherent env) (he : ∀ entry ∈ env.elements.val, Module.Segments.elementValid env entry)
    (hd : ∀ entry ∈ segments, Module.Data.Valid env entry) (index : funcidx) :
    index ∈ env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val) ↔
      index ∈ Spec.DeclaredReferences.declarations (moduleOf (fromEnv env tables memories codes segments)) := by
  have helem : env.elements.val.flatMap (fun e =>
      Spec.DeclaredReferences.elementIndices (Module.Elaboration.element (Module.Environment.rawElement e))) =
      env.elements.val.flatMap (fun e => (element e).map (fun idx => uN.mk_uN idx.val)) := by
    apply List.flatMap_congr
    intro e hm
    exact element_indices (he e hm)
  have hdata : segments.flatMap (fun d => Spec.DeclaredReferences.dataIndices (Module.Data.translate (Module.Data.raw d))) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro d hm
    exact data_indices (hd d hm)
  change env.declared_funcs.val = collected env at hc
  rw [hc]
  simp only [collected, List.map_append, List.map_flatMap,
    Spec.DeclaredReferences.declarations, moduleOf, fromEnv, List.flatMap_map,
    global_indices, export_indices, helem, hdata, List.append_nil,
    List.mem_append]
  tauto

end Itasca.Module.References

end

/-! ## CodeEntry -/

section

/-!
# Module-level restrictions

`Restrictions` collects the explicit conditions on a raw module that the
generated 2.0 judgment does not express: `ModuleConditions` and declared function references. The theorem `restrictions`
derives it for a valid cached environment with typed code entries, and `elaborates` shows such a
module elaborates with in-bounds type references.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- Distinct export byte names in a valid environment have distinct decoded names. -/
theorem export_names_distinct {env : metadata.Env} (hv : Module.Environment.Valid env) :
    (env.exports.val.map (fun e => Binary.nameOfBytes e.name.val)).Nodup := by
  have h := hv.distinctExports.map_on (f := Binary.nameOfBytes) ?_
  · simpa [List.map_map, Function.comp_def] using h
  · intro x hx y hy he
    obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ey, hey, rfl⟩ := List.mem_map.mp hy
    exact (hv.exportNames ex hex).name_of_bytes_injective (hv.exportNames ey hey) he

/-- A valid cached environment with typed code entries gives the module-level `Restrictions` of the
module it describes. -/
theorem restrictions {env tables memories codes segments}
    (hc : Module.Environment.Cache env tables memories) (hv : Module.Environment.Valid env)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes) :
    Restrictions (fromEnv env tables memories codes segments) := by
  constructor
  · constructor
    · simpa [fromEnv, Module.Environment.rawExport, List.map_map, Function.comp_def] using export_names_distinct hv
    · have h := hv.memoryCount
      rw [hc.memories, List.length_append] at h
      simpa [fromEnv, Module.Environment.rawImport, List.map_map, Function.comp_def, mems_imports] using h
  · change ∀ f ∈ List.zipWith CodeEntry.function env.func_type_indices.val codes,
      Spec.DeclaredReferences.Function _ f
    have hall : ∀ f ∈ List.zipWith CodeEntry.function env.func_type_indices.val codes,
        Spec.DeclaredReferences.Function
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
    exact (hall f hf).mono (Module.References.coherent_declared hv.references)

/-- A cached environment with typed code entries elaborates its module with in-bounds type
references and matching code counts. -/
theorem elaborates {env tables memories codes segments}
    (hc : Module.Environment.Cache env tables memories)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes) :
    Elaborates (fromEnv env tables memories codes segments)
      (moduleOf (fromEnv env tables memories codes segments)) := by
  constructor
  · rfl
  · intro entry he idx hidx
    change entry ∈ env.imports.val.map Module.Environment.rawImport at he
    obtain ⟨e, hmem, heq⟩ := (List.mem_map.mp he : ∃ e ∈ env.imports.val, Module.Environment.rawImport e = entry)
    subst entry
    apply hc.import_indices idx
    simp only [Module.Environment.importedFuncs, List.mem_filterMap]
    exact ⟨e, hmem, by simp [Module.Environment.rawImport] at hidx; simp [hidx]⟩
  · intro idx hi
    change idx ∈ env.func_type_indices.val at hi
    change idx.val < env.types.val.length
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hi
    have hc' := hcodes.get hj (by rw [← hcodes.length_eq]; exact hj)
    simpa [List.get_eq_getElem, he] using hc'.type_lt
  · exact hcodes.length_eq

end Itasca.Module.Elaboration

end

end

/-! ## FromTyping -/

section

/-!
# Requirements derived from generated typing

Generated section typing determines function types and section prerequisites. Cached
environments, accessor types and raw-module metadata retain the same independent source
witnesses.
-/

/-! ## Metadata -/

section

/-!
# Returned metadata

`Matches` says the environment and tail the validator returns describe exactly a raw module, and
`AccessorTypes` says the results of `metadata.Env.import_types` and `metadata.Env.export_types` agree with the
elaborated module's import types and typed exports. `contextOf` is the module context computed from
the raw module alone, and `accessor_types` and `matches_from_env` establish these properties for a
valid cached environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- For a cached environment, the raw module's own context is `moduleContext`. -/
theorem context_of_from_env {env tables memories codes segments}
    (hc : Module.Environment.Cache env tables memories) :
    contextOf (fromEnv env tables memories codes segments) =
      moduleContext env (Translation.Environment.elementTypes env) segments.length := by
  symm
  simpa [contextOf, fromEnv, importTypes, Module.Environment.rawImport, Module.Environment.rawElement,
    Translation.Environment.elementTypes, List.map_map, Function.comp_def]
    using module_context_eq hc (Translation.Environment.elementTypes env) segments.length

/-- Resolved import types translate to the elaborated import types. -/
theorem import_types_resolved {env entries xts}
    (h : List.Forall₂ (Module.Externals.ImportResolves env) entries xts) :
    xts.map Module.Externals.externalType = entries.map (fun e => importType env.types.val e.desc) := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp [import_type_resolved hp, ih]

/-- A valid cached environment with well-formed export names has `AccessorTypes` for the module it
describes. -/
theorem accessor_types {env tables memories codes segments}
    (hc : Module.Environment.Cache env tables memories) (hv : Module.Environment.Valid env)
    (hn : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val)) :
    AccessorTypes env (fromEnv env tables memories codes segments) := by
  obtain ⟨ixts, hi⟩ := hc.imports_resolve
  obtain ⟨exts, he⟩ := hv.exports_resolve
  obtain ⟨ir, hir, imports, rfl, hiEq⟩ := WP.spec_imp_exists (metadata.Env.import_types.resolved env ixts hi)
  obtain ⟨er, her, exports, rfl, heEq⟩ := WP.spec_imp_exists (metadata.Env.export_types.resolved env exts he)
  refine ⟨imports, exports, hir, her, ?_, ?_⟩
  · simpa [hiEq, fromEnv, Module.Environment.rawImport, List.map_map, Function.comp_def] using import_types_resolved hi
  · rw [heEq, context_of_from_env hc]
    simpa [fromEnv, List.map_map, Function.comp_def] using
      exports_typed he hn _ (module_context_matches env (Translation.Environment.elementTypes env) segments.length)

/-- A cached environment and tail match the module `fromEnv` builds from them. -/
theorem matches_from_env {env tables memories codes} (tail : metadata.Tail)
    (hc : Module.Environment.Cache env tables memories) :
    Matches env tail (fromEnv env tables memories codes tail.data.val) := ⟨rfl, hc⟩

end Itasca.Module.Elaboration

end

/-! ## TypingInversion -/

section

/-!
# Inversion of `Module_ok`

`sections_of_typing` recovers `SectionsTyped`, the canonical typing of every section, from
`Module_ok` of an elaborated module. The contexts are computed from the raw module alone
(`contextOf`, `initializerContextOf`), so the result does not depend on any validator output.
`function_type_of_typing` and `function_lists_of_typing` identify the function types of typed code
entries.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- The generated `Forall₂` of a list pair gives `List.Forall₂` when the lengths agree. -/
theorem forall₂_of_generated {α β : Type} {R : α → β → Prop} {xs ys}
    (hn : xs.length = ys.length) (h : Forall₂ R xs ys) : List.Forall₂ R xs ys :=
  List.forall₂_iff_zip.mpr ⟨hn, fun {_ _} hm => h _ hm⟩

theorem eq_map_left {α β γ : Type} {R : α → β → Prop} {xs : List α} {ys : List γ}
    {g : γ → β} {f : γ → α} (h : List.Forall₂ R xs (ys.map g))
    (hf : ∀ a b, R a (g b) → a = f b) : xs = ys.map f := by
  induction ys generalizing xs with
  | nil => cases h; rfl
  | cons y ys ih =>
    cases h with
    | cons hp ht => simp [hf _ _ hp, ih ht]

theorem eq_map_right {α β γ : Type} {R : α → β → Prop} {xs : List γ} {ys : List β}
    {f : γ → α} {g : γ → β} (h : List.Forall₂ R (xs.map f) ys)
    (hg : ∀ a b, R (f a) b → b = g a) : ys = xs.map g :=
  eq_map_left h.flip (fun b a hp => hg a b hp)

/-- The initializer context computed from the raw module: its imported globals only, and no
segment spaces. -/
def initializerContextOf (raw : Binary.Module) : context :=
  { contextOf raw with
    GLOBALS := Module.Translation.globals (raw.imports.map (fun e => importType raw.types e.desc))
    ELEMS := [], DATAS := [] }

/-- The canonical section judgments recovered from generated module typing. The contexts are
computed from the independent raw module and not from parser output. -/
structure SectionsTyped (raw : Binary.Module) : Prop where
  imports : ∀ e ∈ raw.imports, Externtype_ok (importType raw.types e.desc)
  globals : ∀ g ∈ raw.globals,
    Global_ok (initializerContextOf raw) (Module.Constants.global g) (Translation.globalType g.gtype)
  tables : ∀ tt ∈ raw.tables, Tabletype_ok (Translation.Environment.tableType tt)
  memories : ∀ mt ∈ raw.memories, Memtype_ok (Translation.Environment.memType mt)
  elements : ∀ e ∈ raw.elements,
    Elem_ok (initializerContextOf raw) (element e) (Translation.referenceType e.elem)
  data : ∀ d ∈ raw.data, Data_ok (initializerContextOf raw) (Module.Data.translate d)
  functions : List.Forall₂
    (fun idx entry => Func_ok (contextOf raw) (CodeEntry.function idx entry) (functionType raw.types idx))
    raw.functions raw.codes
  start : ∀ idx, raw.start = some idx → Start_ok (contextOf raw) (start idx)
  exports : ∀ e ∈ raw.exports, ∃ xt, Export_ok (contextOf raw) (exportDecl e) xt

/-- Inversion of `Func_ok`: the type index is in range. -/
theorem func_index_bound {C : context} {f ft} (h : Func_ok C f ft) :
    match f with | .FUNC idx _ _ => proj_uN_0 idx < C.TYPES.length := by
  cases h
  assumption

/-- Inversion of `Func_ok`: the function type is the context's type at the type index. -/
theorem func_type_lookup {C : context} {f ft} (h : Func_ok C f ft) :
    match f with | .FUNC idx _ _ => ft = C.TYPES[proj_uN_0 idx]! := by
  cases h
  dsimp only
  symm
  assumption

/-- A typed code entry in a context with translated types has the type given by `functionType`. -/
theorem function_type_of_typing {C : context} {ts : List wasm_types.FuncType} {idx entry ft}
    (h : Func_ok C (CodeEntry.function idx entry) ft)
    (hC : C.TYPES = ts.map Translation.Environment.funcType) : ft = functionType ts idx := by
  have hi := func_index_bound h
  have he := func_type_lookup h
  have hidx : idx.val < ts.length := by simpa [CodeEntry.function, hC, proj_uN_0] using hi
  rw [function_type_lookup hidx]
  change ft = C.TYPES[idx.val]! at he
  rw [hC, getElem!_pos _ _ (by simpa using hidx), List.getElem_map] at he
  exact he

/-- Typed functions in a context with translated types determine the function types of their type
indices, and each entry is typed at its own type. -/
theorem function_lists_of_typing {C : context} {ts : List wasm_types.FuncType} {indices codes fts}
    (hn : indices.length = codes.length)
    (h : List.Forall₂ (fun ft f => Func_ok C f ft) fts (List.zipWith CodeEntry.function indices codes))
    (hC : C.TYPES = ts.map Translation.Environment.funcType) :
    fts = indices.map (functionType ts) ∧
    List.Forall₂ (fun idx entry => Func_ok C (CodeEntry.function idx entry) (functionType ts idx)) indices codes := by
  induction indices generalizing codes fts with
  | nil =>
    cases codes with
    | nil => cases h; exact ⟨rfl, .nil⟩
    | cons _ _ => simp at hn
  | cons idx indices ih =>
    cases codes with
    | nil => simp at hn
    | cons entry codes =>
      cases h with
      | cons hp ht =>
        obtain ⟨heq, hrest⟩ := ih (by simpa using hn) ht
        have he := function_type_of_typing hp hC
        exact ⟨by simp [he, heq], .cons (he ▸ hp) hrest⟩

/-- `Module_ok` of an elaborated module gives `SectionsTyped` for the raw module. -/
theorem sections_of_typing {raw : Binary.Module}
    (he : Elaborates raw (moduleOf raw)) (h : Module_ok (moduleOf raw)) : SectionsTyped raw := by
  unfold moduleOf at h
  cases h
  rename_i n fts ixt C' gts tts mts rts C ftdefs xts ifts igts itts imts v3 v2 v1 v0
    hmproj htproj hgproj hfproj hmemcap hC hC' hif hig hit him hwi hwC' hwC hwx hwtab hwmem
    hwimport hwfull hwinit htylen htys himplen himps hfunlen hfuns hgloblen hglobs
    htablen htabs hmemlen hmems helemlen helems hdatas hn hstarts hexplen hexps hwmodule
  have htys' := forall₂_of_generated htylen htys
  have hfts : fts = raw.types.map Translation.Environment.funcType :=
    eq_map_left htys' (fun _ _ hp => by cases hp; rfl)
  have himps' := forall₂_of_generated himplen himps
  have hixt : ixt = raw.imports.map (fun e => importType raw.types e.desc) :=
    eq_map_right himps' (fun _ _ hp => by cases hp; rfl)
  have hglobs' := forall₂_of_generated hgloblen hglobs
  have hgts : gts = raw.globals.map (fun g => Translation.globalType g.gtype) :=
    eq_map_right hglobs' (fun _ _ hp => by cases hp; rfl)
  have htabs' := forall₂_of_generated htablen htabs
  have htts : tts = raw.tables.map Translation.Environment.tableType :=
    eq_map_right htabs' (fun _ _ hp => by cases hp; rfl)
  have hmems' := forall₂_of_generated hmemlen hmems
  have hmts : mts = raw.memories.map Translation.Environment.memType :=
    eq_map_right hmems' (fun _ _ hp => by cases hp; rfl)
  have helems' := forall₂_of_generated helemlen helems
  have hrts : rts = raw.elements.map (fun entry => Translation.referenceType entry.elem) :=
    eq_map_right helems' (fun _ _ hp => by cases hp; rfl)
  have hfuns' := forall₂_of_generated hfunlen hfuns
  have hCtypes : C.TYPES = raw.types.map Translation.Environment.funcType := by rw [hC]; exact hfts
  obtain ⟨hftdefs, hfunctions⟩ := function_lists_of_typing he.code_count hfuns' hCtypes
  have hifs : ifts = Module.Translation.funcs ixt := hif.trans (Module.Translation.funcs_unique hfproj)
  have higs : igts = Module.Translation.globals ixt := hig.trans (Module.Translation.globals_unique hgproj)
  have hits : itts = Module.Translation.tables ixt := hit.trans (Module.Translation.tables_unique htproj)
  have hims : imts = Module.Translation.mems ixt := him.trans (Module.Translation.mems_unique hmproj)
  have hCe : C = contextOf raw := by
    simp only [hC, contextOf, hfts, hftdefs, hgts, htts, hmts, hrts,
      hifs, higs, hits, hims, hixt, hn, List.length_map]
  have hC'e : C' = initializerContextOf raw := by
    simp only [hC', initializerContextOf, contextOf, hfts, hftdefs, htts, hmts,
      hifs, higs, hits, hims, hixt]
  constructor
  · have hh := forall₂_left himps' (fun i => match i with | .IMPORT _ _ xt => Externtype_ok xt)
      (fun _ _ hp => by cases hp; assumption)
    intro e he
    exact hh (importDecl raw.types e) (List.mem_map.mpr ⟨e, he, rfl⟩)
  · rw [hgts, hC'e] at hglobs'
    have hh := List.forall₂_map_left_iff.mp hglobs'
    have hh := List.forall₂_map_right_iff.mp hh
    exact fun g hg => (List.forall₂_same.mp hh) g hg
  · have hh := forall₂_left htabs' (fun t => match t with | .TABLE tt => Tabletype_ok tt)
      (fun _ _ hp => by cases hp; assumption)
    intro tt ht
    exact hh (table tt) (List.mem_map.mpr ⟨tt, ht, rfl⟩)
  · have hh := forall₂_left hmems' (fun m => match m with | .MEMORY mt => Memtype_ok mt)
      (fun _ _ hp => by cases hp; assumption)
    intro mt hm
    exact hh (memory mt) (List.mem_map.mpr ⟨mt, hm, rfl⟩)
  · rw [hrts, hC'e] at helems'
    have hh := List.forall₂_map_left_iff.mp helems'
    have hh := List.forall₂_map_right_iff.mp hh
    exact fun e he => (List.forall₂_same.mp hh) e he
  · intro d hd
    rw [← hC'e]
    exact hdatas _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
  · simpa [hCe] using hfunctions
  · intro idx hs
    rw [← hCe]
    exact hstarts _ (by simp [hs])
  · have hh := forall₂_left (forall₂_of_generated hexplen hexps)
      (fun e => ∃ xt, Export_ok C e xt) (fun _ xt hp => ⟨xt, hp⟩)
    intro e he
    simpa [hCe] using hh (exportDecl e) (List.mem_map.mpr ⟨e, he, rfl⟩)

end Itasca.Module.Elaboration

end

end
