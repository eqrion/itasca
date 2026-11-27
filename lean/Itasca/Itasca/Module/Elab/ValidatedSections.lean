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

Validated section metadata and code entries establish the generated module typing judgment and its declared-reference restrictions.
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
theorem import_type_resolved {env : metadata.CodeMetadata} {entry : Binary.Import} {xt : wasm_types.ExternType}
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
theorem export_index_typed {env : metadata.CodeMetadata} {entry : metadata.Export} {xt : wasm_types.ExternType}
    (h : Module.Externals.ExportResolves env entry xt)
    (C : context) (hC : CodeEntry.ModuleContext env C) :
    Externidx_ok C (exportIndex entry.desc) (Module.Externals.externalType xt) := by
  cases hd : entry.desc with
  | Func idx =>
    cases lookup : env.funcs.val[idx.val]? with
    | none => simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
    | some d =>
      cases ft : env.types.val[d.type_index.val]? with
      | none => simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup, ft] at h
      | some ty =>
        simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup, ft] at h
        subst xt
        obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp lookup
        apply Externidx_ok.func C _ _
        · simpa [hC.funcs, proj_uN_0] using hi
        · simp only [hC.funcs, proj_uN_0]
          rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, he]
          simp [Translation.Environment.descriptorType, ft]
        · exact hC.wf
        · simpa [hd, exportIndex] using export_index_wf entry.desc
        · exact .externtype_case_0 _
  | Table idx =>
    cases lookup : env.tables.val[idx.val]? with
    | none => simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
    | some d =>
      simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
      subst xt
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp lookup
      apply Externidx_ok.table C _ _
      · simpa [hC.tables, proj_uN_0] using hi
      · simp only [hC.tables, proj_uN_0]
        rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, he]
      · exact hC.wf
      · simpa [hd, exportIndex] using export_index_wf entry.desc
      · exact .externtype_case_2 _ (Translation.Environment.table_type_wf _)

  | Memory idx =>
    cases lookup : env.memories.val[idx.val]? with
    | none => simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
    | some d =>
      simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
      subst xt
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp lookup
      apply Externidx_ok.mem C _ _
      · simpa [hC.mems, proj_uN_0] using hi
      · simp only [hC.mems, proj_uN_0]
        rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, he]
      · exact hC.wf
      · simpa [hd, exportIndex] using export_index_wf entry.desc
      · exact .externtype_case_3 _ (Translation.Environment.mem_type_wf _)

  | Global idx =>
    cases lookup : env.globals.val[idx.val]? with
    | none => simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
    | some d =>
      simp [Module.Externals.ExportResolves, hd, metadata.CodeMetadata.externalTypeAt, lookup] at h
      subst xt
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp lookup
      apply Externidx_ok.global C _ _
      · simpa [hC.globals, proj_uN_0] using hi
      · simp only [hC.globals, proj_uN_0]
        rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, he]
      · exact hC.wf
      · simpa [hd, exportIndex] using export_index_wf entry.desc
      · exact .externtype_case_1 _

/-- A resolved export with a well-formed name is typed in the module context. -/
theorem export_typed {env : metadata.CodeMetadata} {entry : metadata.Export} {xt : wasm_types.ExternType}
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
theorem import_type_wf (types : List wasm_types.FuncType) (desc : Binary.ImportDesc) :
    wf_externtype (importType types desc) := by
  cases desc with
  | Func idx => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (Translation.Environment.table_type_wf tt)
  | Memory mt => exact .externtype_case_3 _ (Translation.Environment.mem_type_wf mt)

/-- The external type of each import of a valid cached environment is valid. -/
theorem import_type_valid {env : metadata.ModuleMetadata metadata.CodeMetadata} {imports functions globals tables memories entry}
    (hc : Module.Environment.Cache env.code imports functions globals tables memories) (hv : Module.Environment.Valid env)
    (he : entry ∈ imports) : Externtype_ok (importType env.code.types.val entry.desc) := by
  cases hd : entry.desc with
  | Func idx => exact .func _ (function_type_valid _ _) (.externtype_case_0 _)
  | Global gt => exact .global _ (Translation.global_type_valid gt) (.externtype_case_1 _)
  | Table tt =>
    have hi : tt ∈ Module.Environment.importedTables imports := by
      simp only [Module.Environment.importedTables, List.mem_filterMap]
      exact ⟨entry, he, by simp [hd]⟩
    have member : (tt,true) ∈ env.code.tables.val.map (fun d => (d.ty,d.is_imported)) := by
      rw [hc.tableEntries]; exact List.mem_append_left _ (List.mem_map_of_mem hi)
    obtain ⟨d, hd, eq⟩ := List.mem_map.mp member
    have same : d.ty = tt := congrArg Prod.fst eq
    have limits := hv.tables d hd
    rw [same] at limits
    exact .table _ (Module.Translation.table_type_valid tt limits)
      (.externtype_case_2 _ (Translation.Environment.table_type_wf tt))
  | Memory mt =>
    have hi : mt ∈ Module.Environment.importedMems imports := by
      simp only [Module.Environment.importedMems, List.mem_filterMap]
      exact ⟨entry, he, by simp [hd]⟩
    have member : (mt,true) ∈ env.code.memories.val.map (fun d => (d.ty,d.is_imported)) := by
      rw [hc.memoryEntries]; exact List.mem_append_left _ (List.mem_map_of_mem hi)
    obtain ⟨d, hd, eq⟩ := List.mem_map.mp member
    have same : d.ty = mt := congrArg Prod.fst eq
    have limits := hv.memories d hd
    rw [same] at limits
    exact .mem _ (Module.Translation.mem_type_valid mt limits)
      (.externtype_case_3 _ (Translation.Environment.mem_type_wf mt))

/-- Each import of a valid cached environment is typed, given well-formed names. -/
theorem import_typed {env : metadata.ModuleMetadata metadata.CodeMetadata} {imports functions globals tables memories entry}
    (hc : Module.Environment.Cache env.code imports functions globals tables memories) (hv : Module.Environment.Valid env)
    (he : entry ∈ imports)
    (hmod : wf_name (Binary.nameOfBytes entry.moduleName))
    (hn : wf_name (Binary.nameOfBytes entry.name))
    (C : context) (hC : wf_context C) :
    Import_ok C (importDecl env.code.types.val entry)
      (importType env.code.types.val entry.desc) := by
  exact .mk_Import_ok C _ _ _ (import_type_valid hc hv he) hC
    (.import_case_0 _ _ _ hmod hn (import_type_wf _ _))

/-- The start function of a valid environment is typed in the module context. -/
theorem start_typed {env : metadata.ModuleMetadata metadata.CodeMetadata} (hv : Module.Environment.Valid env) (idx : U32)
    (hs : env.code.start = some idx) (C : context) (hC : CodeEntry.ModuleContext env.code C) :
    Start_ok C (start idx) := by
  obtain ⟨ft, lookup, hp, hr⟩ := hv.start idx hs
  cases hd : env.code.funcs.val[idx.val]? with
  | none => simp [metadata.CodeMetadata.externalTypeAt, hd] at lookup
  | some d =>
    cases ht : env.code.types.val[d.type_index.val]? with
    | none => simp [metadata.CodeMetadata.externalTypeAt, hd, ht] at lookup
    | some ty =>
      simp [metadata.CodeMetadata.externalTypeAt, hd, ht] at lookup
      subst ty
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hd
      apply Start_ok.mk_Start_ok C _
      · simpa [hC.funcs, proj_uN_0] using hi
      · simp only [hC.funcs, proj_uN_0]
        rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map, he]
        simp [Translation.Environment.descriptorType, Translation.Environment.funcType, ht, hp, hr]
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
def importTypes (types : List wasm_types.FuncType) (imports : List Binary.Import) : List externtype :=
  imports.map (fun entry => importType types entry.desc)

/-- The function space translated from import types is the translation of `importedFuncs`. -/
theorem funcs_imports (types : List wasm_types.FuncType) (entries : List Binary.Import) :
    Module.Translation.funcs (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedFuncs entries).map (functionType types) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedFuncs, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.funcs, importType, Module.Environment.importedFuncs, hd, ih]

/-- The global space translated from import types is the translation of `importedGlobals`. -/
theorem globals_imports (types : List wasm_types.FuncType) (entries : List Binary.Import) :
    Module.Translation.globals (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedGlobals entries).map Translation.globalType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedGlobals, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.globals, importType, Module.Environment.importedGlobals, hd, ih]

/-- The table space translated from import types is the translation of `importedTables`. -/
theorem tables_imports (types : List wasm_types.FuncType) (entries : List Binary.Import) :
    Module.Translation.tables (entries.map (fun entry => importType types entry.desc)) =
      (Module.Environment.importedTables entries).map Translation.Environment.tableType := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Module.Environment.importedTables, importType] at ih
    cases hd : entry.desc <;>
      simp [Module.Translation.tables, importType, Module.Environment.importedTables, hd, ih]

/-- The memory space translated from import types is the translation of `importedMems`. -/
theorem mems_imports (types : List wasm_types.FuncType) (entries : List Binary.Import) :
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
theorem funcs_cache {env imports functions globals tables memories}
    (h : Module.Environment.Cache env imports functions globals tables memories) :
    env.funcs.val.map (Translation.Environment.descriptorType env.types.val) =
      Module.Translation.funcs (importTypes env.types.val imports) ++ functions.map (functionType env.types.val) := by
  rw [importTypes, funcs_imports]
  change env.funcs.val.map (fun d => functionType env.types.val d.type_index) = _
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map (functionType env.types.val)) h.funcs

/-- The translated global index space contains imports followed by definitions. -/
theorem globals_cache {env imports functions globals tables memories}
    (h : Module.Environment.Cache env imports functions globals tables memories) :
    env.globals.val.map (fun d => Translation.globalType d.gtype) =
      Module.Translation.globals (importTypes env.types.val imports) ++
        globals.map (fun g => Translation.globalType g.gtype) := by
  rw [importTypes, globals_imports]
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map (fun d => Translation.globalType d.1)) h.globalEntries

/-- The translated table index space contains imports followed by definitions. -/
theorem tables_cache {env imports functions globals tables memories}
    (h : Module.Environment.Cache env imports functions globals tables memories) :
    env.tables.val.map (fun d => Translation.Environment.tableType d.ty) =
      Module.Translation.tables (importTypes env.types.val imports) ++
        tables.map Translation.Environment.tableType := by
  rw [importTypes, tables_imports]
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map (fun d => Translation.Environment.tableType d.1)) h.tableEntries

/-- The translated memory index space contains imports followed by definitions. -/
theorem memories_cache {env imports functions globals tables memories}
    (h : Module.Environment.Cache env imports functions globals tables memories) :
    env.memories.val.map (fun d => Translation.Environment.memType d.ty) =
      Module.Translation.mems (importTypes env.types.val imports) ++
        memories.map Translation.Environment.memType := by
  rw [importTypes, mems_imports]
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map (fun d => Translation.Environment.memType d.1)) h.memoryEntries

/-- The typing context for functions, elements, segments and exports: the environment's translated
index spaces, the given element types and `dataCount` data segments, and no locals or labels. -/
def moduleContext (env : metadata.CodeMetadata) (elementTypes : List elemtype) (dataCount : Nat) : context :=
  { TYPES := env.types.val.map Translation.Environment.funcType
    FUNCS := env.funcs.val.map (Translation.Environment.descriptorType env.types.val)
    GLOBALS := env.globals.val.map (fun d => Translation.globalType d.gtype)
    TABLES := env.tables.val.map (fun d => Translation.Environment.tableType d.ty)
    MEMS := env.memories.val.map (fun d => Translation.Environment.memType d.ty)
    ELEMS := elementTypes
    DATAS := List.replicate dataCount datatype.OK
    LOCALS := []
    LABELS := []
    RETURN := none }

/-- The typing context for constant initializers: `moduleContext` with no segment spaces and only
the imported globals. -/
def initializerContext (env : metadata.CodeMetadata) : context :=
  { moduleContext env [] 0 with
    GLOBALS := (env.globals.val.take env.num_imported_globals.val).map (fun d => Translation.globalType d.gtype) }

/-- `moduleContext` is a `CodeEntry.ModuleContext` for the environment. -/
theorem module_context_matches (env : metadata.CodeMetadata) (elementTypes : List elemtype) (dataCount : Nat) :
    CodeEntry.ModuleContext env (moduleContext env elementTypes dataCount) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `moduleContext` is well formed. -/
theorem module_context_wf (env : metadata.CodeMetadata) (elementTypes : List elemtype) (dataCount : Nat) :
    wf_context (moduleContext env elementTypes dataCount) :=
  (module_context_matches env elementTypes dataCount).wf

/-- `initializerContext` is well formed. -/
theorem initializer_context_wf (env : metadata.CodeMetadata) : wf_context (initializerContext env) := by
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
theorem element_typed {env : metadata.ModuleMetadata metadata.CodeMetadata} (hv : Module.Environment.Valid env)
    (entry : metadata.Element) (he : entry ∈ env.elements.val) :
    Elem_ok (initializerContext env.code) (element (Module.Environment.rawElement entry))
      (Translation.referenceType entry.elem) := by
  exact (hv.elements entry he).typed (initializerContext env.code) (initializer_context_wf env.code)
    rfl rfl rfl

/-- Each defined table of a valid cached environment is typed in any well-formed context. -/
theorem table_typed {env : metadata.ModuleMetadata metadata.CodeMetadata} {imports functions globals tables memories}
    (hc : Module.Environment.Cache env.code imports functions globals tables memories)
     (hv : Module.Environment.Valid env) (tt : wasm_types.TableType) (ht : tt ∈ tables)
    (C : context) (hC : wf_context C) :
    Table_ok C (table tt) (Translation.Environment.tableType tt) := by
  have mem : (tt,false) ∈ env.code.tables.val.map (fun d => (d.ty,d.is_imported)) := by
    rw [hc.tableEntries]; exact List.mem_append_right _ (List.mem_map_of_mem ht)
  obtain ⟨d, hm, eq⟩ := List.mem_map.mp mem
  have same : d.ty = tt := congrArg Prod.fst eq
  have limits := hv.tables d hm
  rw [same] at limits
  exact .mk_Table_ok C _ (Module.Translation.table_type_valid tt limits) hC
    (.table_case_0 _ (Translation.Environment.table_type_wf tt))

/-- Each defined memory of a valid cached environment is typed in any well-formed context. -/
theorem memory_typed {env : metadata.ModuleMetadata metadata.CodeMetadata} {imports functions globals tables memories}
    (hc : Module.Environment.Cache env.code imports functions globals tables memories)
     (hv : Module.Environment.Valid env) (mt : wasm_types.MemType) (ht : mt ∈ memories)
    (C : context) (hC : wf_context C) :
    Mem_ok C (memory mt) (Translation.Environment.memType mt) := by
  have mem : (mt,false) ∈ env.code.memories.val.map (fun d => (d.ty,d.is_imported)) := by
    rw [hc.memoryEntries]; exact List.mem_append_right _ (List.mem_map_of_mem ht)
  obtain ⟨d, hm, eq⟩ := List.mem_map.mp mem
  have same : d.ty = mt := congrArg Prod.fst eq
  have limits := hv.memories d hm
  rw [same] at limits
  exact .mk_Mem_ok C _ (Module.Translation.mem_type_valid mt limits) hC
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

/-- Reconstruct the raw module with the declaration witnesses for indices and import payloads. -/
def fromEnv (env : metadata.ModuleMetadata metadata.CodeMetadata) (decls : Module.Environment.Declarations)
    (codes : List Binary.Code) (segments : List metadata.Data) : Binary.Module :=
  ⟨env.code.types.val, decls.imports, decls.functions, decls.tables, decls.memories, decls.globals,
    env.exports.val.map Module.Environment.rawExport, env.code.start, env.elements.val.map Module.Environment.rawElement,
    env.code.data_count, codes, segments.map Module.Data.raw⟩

theorem represents_module {env decls codes segments} (h : Module.Environment.Represents env decls) :
    decls.module codes (segments.map Module.Data.raw) = fromEnv env decls codes segments := by
  simp [Module.Environment.Declarations.module, fromEnv, h.types, h.exports, h.start, h.elements, h.dataCount]

/-- The context for import typing: only the module's types. -/
def importContext (env : metadata.CodeMetadata) : context :=
  ⟨env.types.val.map Translation.Environment.funcType, [], [], [], [], [], [], [], [], none⟩

/-- The import context is well formed. -/
theorem import_context_wf (env : metadata.CodeMetadata) : wf_context (importContext env) := by
  constructor <;> simp [Forall]

/-- For a cached environment, `moduleContext` is the imported spaces followed by the defined
spaces, with the given element spaces and data count. -/
theorem module_context_eq {env imports functions globals tables memories}
    (hc : Module.Environment.Cache env imports functions globals tables memories)
    (es : List elemtype) (nd : Nat) :
    moduleContext env es nd =
      ⟨env.types.val.map Translation.Environment.funcType,
        Module.Translation.funcs (importTypes env.types.val imports) ++ functions.map (functionType env.types.val),
        Module.Translation.globals (importTypes env.types.val imports) ++ globals.map (fun g => Translation.globalType g.gtype),
        Module.Translation.tables (importTypes env.types.val imports) ++ tables.map Translation.Environment.tableType,
        Module.Translation.mems (importTypes env.types.val imports) ++ memories.map Translation.Environment.memType,
        es, List.replicate nd .OK, [], [], none⟩ := by
  simp only [moduleContext, funcs_cache hc, globals_cache hc, tables_cache hc, memories_cache hc]

/-- For a cached environment, `initializerContext` has the imported globals only and no local,
label or segment spaces. -/
theorem initializer_context_eq {env imports functions globals tables memories}
    (hc : Module.Environment.Cache env imports functions globals tables memories) :
    initializerContext env =
      ⟨env.types.val.map Translation.Environment.funcType,
        Module.Translation.funcs (importTypes env.types.val imports) ++ functions.map (functionType env.types.val),
        Module.Translation.globals (importTypes env.types.val imports),
        Module.Translation.tables (importTypes env.types.val imports) ++ tables.map Translation.Environment.tableType,
        Module.Translation.mems (importTypes env.types.val imports) ++ memories.map Translation.Environment.memType,
        [], [], [], [], none⟩ := by
  have globalPrefix : (env.globals.val.take env.num_imported_globals.val).map (fun d => Translation.globalType d.gtype) =
      (Module.Environment.importedGlobals imports).map Translation.globalType := by
    have eq := congrArg (List.take env.num_imported_globals.val) hc.globalEntries
    rw [← List.map_take, hc.numGlobals] at eq
    have len : (Module.Environment.importedGlobals imports).length =
        ((Module.Environment.importedGlobals imports).map fun ty => (ty, (none : Option wasm_types.ConstExpr))).length := by simp
    rw [len, List.take_left] at eq
    rw [hc.numGlobals]
    simpa [List.map_map, Function.comp_def] using congrArg (List.map (fun d => Translation.globalType d.1)) eq
  simp only [initializerContext, moduleContext, funcs_cache hc, tables_cache hc,
    memories_cache hc, globalPrefix, importTypes, globals_imports, List.replicate_zero]

/-- A valid cached environment with typed code entries, valid data segments and resolved exports
has `Module_ok` for its elaborated module. All section judgments are assembled in one coherent
module context, and name well-formedness comes from the independent byte grammar. -/
theorem typed {env : metadata.ModuleMetadata metadata.CodeMetadata} {decls codes segments xts}
    (rep : Module.Environment.Represents env decls) (hv : Module.Environment.Valid env)
    (hiNames : ∀ entry ∈ decls.imports,
      wf_name (Binary.nameOfBytes entry.moduleName) ∧ wf_name (Binary.nameOfBytes entry.name))
    (heNames : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val))
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env.code idx entry) decls.functions codes)
    (hsegments : ∀ segment ∈ segments, Module.Data.Valid env.code segment)
    (hdataCount : ∀ count, env.code.data_count = some count → count.val = segments.length)
    (hxts : List.Forall₂ (Module.Externals.ExportResolves env.code) env.exports.val xts) :
    Module_ok (moduleOf (fromEnv env decls codes segments)) := by
  have hc := rep.cache
  have elemTypes : Translation.Environment.elementTypes env.code =
      env.elements.val.map (fun e => Translation.referenceType e.elem) := by
    simp [Translation.Environment.elementTypes, rep.elementTypes, rep.elements,
      List.map_map, Function.comp_def, Module.Environment.rawElement]
  let C := moduleContext env.code (Translation.Environment.elementTypes env.code) segments.length
  let C' := initializerContext env.code
  have hwC := module_context_wf env.code (Translation.Environment.elementTypes env.code) segments.length
  have hwC' := initializer_context_wf env.code
  have hmatch := module_context_matches env.code (Translation.Environment.elementTypes env.code) segments.length
  have hsegmentContext : CodeEntry.SegmentContext env.code C := by
    constructor
    · simp [C, moduleContext]
    · cases hd : env.code.data_count with
      | none => simp [C, moduleContext, Translation.Environment.dataTypes, hd]
      | some count => simp [C, moduleContext, Translation.Environment.dataTypes, hd, hdataCount count hd]
  have htypes := forall₂_map env.code.types.val Translation.Environment.funcType
    (fun ft => type.TYPE (Translation.Environment.funcType ft)) (fun ft ty => Type_ok ty ft)
    (fun ft _ => Type_ok.mk_Type_ok _ (Module.Translation.func_type_valid ft))
  have himports := forall₂_map decls.imports
    (fun e => importDecl env.code.types.val e)
    (fun e => importType env.code.types.val e.desc) (Import_ok (importContext env.code))
    (fun e he => import_typed hc hv he (hiNames e he).1 (hiNames e he).2 _ (import_context_wf env.code))
  have hglobals := forall₂_map decls.globals Module.Constants.global
    (fun g => Translation.globalType g.gtype) (Global_ok C')
    (fun g hg => by
      have mem : (g.gtype, some g.init) ∈ env.code.globals.val.map (fun d => (d.gtype,d.init)) := by
        rw [hc.globalEntries]; exact List.mem_append_right _ (List.mem_map_of_mem hg)
      obtain ⟨d, member, same⟩ := List.mem_map.mp mem
      have gt : d.gtype = g.gtype := congrArg Prod.fst same
      have init : d.init = some g.init := congrArg Prod.snd same
      have valid := hv.globals d member _ init
      rw [gt] at valid
      exact Module.Constants.global_typed env.code g valid C' hwC' rfl rfl)
  have htables := forall₂_map decls.tables table Translation.Environment.tableType (Table_ok C')
    (fun tt ht => table_typed hc hv tt ht C' hwC')
  have hmemories := forall₂_map decls.memories memory Translation.Environment.memType (Mem_ok C')
    (fun mt ht => memory_typed hc hv mt ht C' hwC')
  have helements := forall₂_map env.elements.val (fun e => element (Module.Environment.rawElement e))
    (fun e => Translation.referenceType e.elem) (Elem_ok C') (fun e he => element_typed hv e he)
  have hdatas : Forall (Data_ok C') (segments.map (fun d => Module.Data.translate (Module.Data.raw d))) := by
    simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact (hsegments d hd).typed hv.memoryCount C' hwC' rfl rfl rfl
  have hfuncs := functions_typed hcodes C hmatch hsegmentContext
  have hstart : Forall (Start_ok C) ((env.code.start.map start).toList) := by
    cases hs : env.code.start with
    | none => simp [Forall]
    | some idx => simpa [hs, Forall] using start_typed hv idx hs C hmatch
  have hexports := exports_typed hxts heNames C hmatch
  have hmodule : wf_module (moduleOf (fromEnv env decls codes segments)) := by
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
    (ft'_lst := env.code.types.val.map Translation.Environment.funcType)
    (ixt_lst := importTypes env.code.types.val decls.imports) (C' := C')
    (gt_lst := decls.globals.map (fun g => Translation.globalType g.gtype))
    (tt_lst := decls.tables.map Translation.Environment.tableType) (mt_lst := decls.memories.map Translation.Environment.memType)
    (rt_lst := Translation.Environment.elementTypes env.code) (C := C)
    (ft_lst := decls.functions.map (functionType env.code.types.val))
    (xt_lst := xts.map Module.Externals.externalType)
    (ift_lst := Module.Translation.funcs (importTypes env.code.types.val decls.imports))
    (igt_lst := Module.Translation.globals (importTypes env.code.types.val decls.imports))
    (itt_lst := Module.Translation.tables (importTypes env.code.types.val decls.imports))
    (imt_lst := Module.Translation.mems (importTypes env.code.types.val decls.imports))
    (var_0 := Module.Translation.funcs (importTypes env.code.types.val decls.imports))
    (var_1 := Module.Translation.globals (importTypes env.code.types.val decls.imports))
    (var_2 := Module.Translation.tables (importTypes env.code.types.val decls.imports))
    (var_3 := Module.Translation.mems (importTypes env.code.types.val decls.imports)) (v_n := segments.length)
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
  · simp [elemTypes]
  · simpa [List.map_map, Function.comp_def, elemTypes] using forall₂_generated helements
  · simpa [List.map_map, Function.comp_def] using hdatas
  · exact hfuncs.length_eq
  · exact forall₂_generated hfuncs
  · exact hstart
  · simpa using hxts.length_eq
  · simpa [List.map_map, Function.comp_def] using forall₂_generated hexports
  · have sizes := congrArg List.length hc.memoryEntries
    simp only [List.length_map, List.length_append] at sizes
    have bound := hv.memoryCount
    simp only [List.length_map]
    omega
  · simpa [C, List.map_const'] using module_context_eq hc (Translation.Environment.elementTypes env.code) segments.length
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
  · exact import_context_wf env.code
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
theorem global_indices (entry : Binary.Global) :
    Spec.DeclaredReferences.globalIndices (Module.Constants.global entry) =
      (initializer entry.init).map (fun index => uN.mk_uN index.val) :=
  initializer_indices entry.init

/-- An export's declared indices agree with the SpecTec collector. -/
theorem export_indices (entry : metadata.Export) :
    Spec.DeclaredReferences.exportIndices (exportDecl (Module.Environment.rawExport entry)) =
      (exportIndices entry).map (fun index => uN.mk_uN index.val) := by
  cases h : entry.desc <;>
    simp [Spec.DeclaredReferences.exportIndices, exportDecl, exportIndex,
      Module.Environment.rawExport, exportIndices, h]

private theorem raw_element_refs (e : metadata.Element) :
    (Module.Environment.rawElement e).init.flatMap initializer = element e := by
  cases eq : e.init <;> simp [Module.Environment.rawElement, element, eq, List.flatMap_map, initializer]

private theorem raw_global_refs {env decls} (rep : Module.Environment.Represents env decls) :
    env.code.globals.val.flatMap global = decls.globals.flatMap (fun g => initializer g.init) := by
  have eq := congrArg (List.flatMap (fun g : wasm_types.GlobalType × Option wasm_types.ConstExpr =>
    g.2.toList.flatMap initializer)) rep.cache.globalEntries
  have empty : (Module.Environment.importedGlobals decls.imports).flatMap (fun _ => ([] : List U32)) = [] :=
    List.flatMap_eq_nil_iff.mpr (by simp)
  unfold global
  simpa [List.flatMap_map, Function.comp_def, empty] using eq

/-- An element initializer's declared index is found by the SpecTec collector. -/
theorem element_member {entry : metadata.Element} {idx : U32} (h : idx ∈ element entry) :
    uN.mk_uN idx.val ∈ Spec.DeclaredReferences.elementIndices
      (Module.Elaboration.element (Module.Environment.rawElement entry)) := by
  rw [← raw_element_refs] at h
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
      obtain ⟨hi, ht, ho⟩ := (show ∃ hi : index.val < env.tables.val.length,
        env.tables.val[index.val].ty.elem = entry.elem ∧ Module.Constants.Valid env offset .I32 from by simpa [hm] using h.1)
      simp [Module.Segments.elementMode, Spec.DeclaredReferences.elementModeIndices,
        initializer_indices, valid_i32_initializer ho]
  rw [← raw_element_refs]
  simp [Module.Elaboration.element, Module.Environment.rawElement, Spec.DeclaredReferences.elementIndices,
    hoffset, List.flatMap_map, initializer_indices, List.map_flatMap]

/-- A valid data segment declares no function. -/
theorem data_indices {env entry} (h : Module.Data.Valid env entry) :
    Spec.DeclaredReferences.dataIndices (Module.Data.translate (Module.Data.raw entry)) = [] := by
  cases hm : entry.mode with
  | Passive => simp [Module.Data.translate, Module.Data.raw, hm, Module.Segments.dataMode, Spec.DeclaredReferences.dataIndices]
  | Active index offset =>
    obtain ⟨hi, ho⟩ := (show index.val < env.memories.val.length ∧ Module.Constants.Valid env offset .I32 from by simpa [Module.Data.Valid, hm] using h)
    simp [Module.Data.translate, Module.Data.raw, hm, Module.Segments.dataMode,
      Spec.DeclaredReferences.dataIndices, initializer_indices, valid_i32_initializer ho]

/-- Every function index collected by the environment is declared in the elaborated module.
Offset declarations can only enlarge the declared set, so this implication needs no typing
premise. -/
theorem collected_declared {env decls codes segments} (rep : Module.Environment.Represents env decls)
    {idx : U32} (h : idx ∈ collected env) :
    uN.mk_uN idx.val ∈ Spec.DeclaredReferences.declarations
      (moduleOf (fromEnv env decls codes segments)) := by
  simp only [collected, raw_global_refs rep, List.mem_append] at h
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
theorem coherent_declared {env decls codes segments} (rep : Module.Environment.Represents env decls)
    (h : Coherent env) :
    ∀ index ∈ Translation.Environment.declaredReferences env.code,
      index ∈ Spec.DeclaredReferences.declarations (moduleOf (fromEnv env decls codes segments)) := by
  rintro ⟨i⟩ hm
  obtain ⟨idx, hi, rfl⟩ := (h i).mp hm
  exact collected_declared rep hi

/-- Typing forces every segment offset to be an `i32` constant expression, so all syntactic
function declarations are in the `declared_funcs` cache, and the cache and the declarations have
the same members. -/
theorem coherent_declared_iff {env decls codes segments} (rep : Module.Environment.Represents env decls)
    (hc : Coherent env) (he : ∀ entry ∈ env.elements.val, Module.Segments.elementValid env.code entry)
    (hd : ∀ entry ∈ segments, Module.Data.Valid env.code entry) (index : funcidx) :
    index ∈ Translation.Environment.declaredReferences env.code ↔
      index ∈ Spec.DeclaredReferences.declarations (moduleOf (fromEnv env decls codes segments)) := by
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
  obtain ⟨i⟩ := index
  rw [hc]
  have eq : (∃ idx ∈ collected env, idx.val = i) ↔
      uN.mk_uN i ∈ (collected env).map (fun idx => uN.mk_uN idx.val) := by simp
  rw [eq]
  simp only [collected, raw_global_refs rep, List.map_append, List.map_flatMap,
    Spec.DeclaredReferences.declarations, moduleOf, fromEnv, List.flatMap_map,
    global_indices, export_indices, helem, hdata, List.append_nil, List.mem_append]
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
theorem export_names_distinct {env : metadata.ModuleMetadata metadata.CodeMetadata} (hv : Module.Environment.Valid env) :
    (env.exports.val.map (fun e => Binary.nameOfBytes e.name.val)).Nodup := by
  have h := hv.distinctExports.map_on (f := Binary.nameOfBytes) ?_
  · simpa [List.map_map, Function.comp_def] using h
  · intro x hx y hy he
    obtain ⟨ex, hex, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ey, hey, rfl⟩ := List.mem_map.mp hy
    exact (hv.exportNames ex hex).name_of_bytes_injective (hv.exportNames ey hey) he

/-- A valid cached environment with typed code entries gives the module-level `Restrictions` of the
module it describes. -/
theorem restrictions {env decls codes segments}
    (rep : Module.Environment.Represents env decls) (hv : Module.Environment.Valid env)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env.code idx entry) decls.functions codes) :
    Restrictions (fromEnv env decls codes segments) := by
  constructor
  · constructor
    · simpa [fromEnv, Module.Environment.rawExport, List.map_map, Function.comp_def] using export_names_distinct hv
    · have h := hv.memoryCount
      have sizes := congrArg List.length rep.cache.memoryEntries
      simp only [List.length_map, List.length_append] at sizes
      simpa [fromEnv, mems_imports] using (sizes ▸ h)
  · change ∀ f ∈ List.zipWith CodeEntry.function decls.functions codes,
      Spec.DeclaredReferences.Function _ f
    have hall : ∀ f ∈ List.zipWith CodeEntry.function decls.functions codes,
        Spec.DeclaredReferences.Function
          (Translation.Environment.declaredReferences env.code) f := by
      generalize hi : decls.functions = indices at hcodes ⊢
      clear hi
      induction hcodes with
      | nil => simp
      | cons hp htail ih =>
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hp.declared
        · exact ih f hf
    intro f hf
    exact (hall f hf).mono (Module.References.coherent_declared rep hv.references)

/-- A cached environment with typed code entries elaborates its module with in-bounds type
references and matching code counts. -/
theorem elaborates {env decls codes segments}
    (rep : Module.Environment.Represents env decls) (hv : Module.Environment.Valid env)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env.code idx entry) decls.functions codes) :
    Elaborates (fromEnv env decls codes segments)
      (moduleOf (fromEnv env decls codes segments)) := by
  constructor
  · rfl
  · intro entry he idx hidx
    have mem : idx ∈ Module.Environment.importedFuncs decls.imports := by
      exact List.mem_filterMap.mpr ⟨entry, he, by simp [hidx]⟩
    have hit : idx ∈ env.code.funcs.val.map metadata.FuncDesc.type_index := by
      rw [rep.cache.funcs]; exact List.mem_append_left _ mem
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hit
    exact hv.funcs d hd
  · intro idx hi
    change idx ∈ decls.functions at hi
    change idx.val < env.code.types.val.length
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hi
    have hc' := hcodes.get hj (by rw [← hcodes.length_eq]; exact hj)
    simpa [List.get_eq_getElem, he] using hc'.type_lt
  · exact hcodes.length_eq

end Itasca.Module.Elaboration

end

end
