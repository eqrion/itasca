import Itasca.Module.Elab.ElementTyping
import Itasca.Module.Elab.TypingLists

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
    (hc : ModuleEnv.Cache env tables memories) {profile : ValidationProfile} (hv : ModuleEnv.Valid env profile)
    (hiNames : ∀ entry ∈ env.imports.val,
      wf_name (ModuleBinary.nameOfBytes entry.module.val) ∧ wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (heNames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val codes)
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
