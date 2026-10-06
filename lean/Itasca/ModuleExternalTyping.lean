import Itasca.ModuleElaboration

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

theorem externalType_wf (xt : types.ExternType) : wf_externtype (ModuleExternals.externalType xt) := by
  cases xt with
  | Func ft => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (EnvTranslation.tableType_wf tt)
  | Memory mt => exact .externtype_case_3 _ (EnvTranslation.memType_wf mt)

theorem exportIndex_wf (desc : module.ExportDesc) : wf_externidx (exportIndex desc) := by
  cases desc with
  | Func idx => exact .externidx_case_0 _ (EnvTranslation.index_wf idx)
  | Table idx => exact .externidx_case_2 _ (EnvTranslation.index_wf idx)
  | Memory idx => exact .externidx_case_3 _ (EnvTranslation.index_wf idx)
  | Global idx => exact .externidx_case_1 _ (EnvTranslation.index_wf idx)

theorem importType_resolved {env : module.Env} {entry : module.Import} {xt : types.ExternType}
    (h : ModuleExternals.ImportResolves env entry xt) :
    importType env.types.val entry.desc = ModuleExternals.externalType xt := by
  cases hd : entry.desc with
  | Func idx =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    obtain ⟨hi, rfl⟩ := h
    simp [importType, hd, ModuleExternals.externalType, functionType_lookup hi]
  | Table tt =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    simp [h, hd, importType, ModuleExternals.externalType]
  | Memory mt =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    simp [h, hd, importType, ModuleExternals.externalType]
  | Global gt =>
    simp only [ModuleExternals.ImportResolves, hd] at h
    simp [h, hd, importType, ModuleExternals.externalType]

theorem export_index_typed {env : module.Env} {entry : module.Export} {xt : types.ExternType}
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

theorem export_typed {env : module.Env} {entry : module.Export} {xt : types.ExternType}
    (h : ModuleExternals.ExportResolves env entry xt)
    (hn : wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (C : context) (hC : CodeEntry.ModuleContext env C) :
    Export_ok C (exportDecl (ModuleEnv.rawExport entry)) (ModuleExternals.externalType xt) := by
  exact .mk_Export_ok C _ _ _ (export_index_typed h C hC) hC.wf (externalType_wf xt)
    (.export_case_0 _ _ hn (exportIndex_wf entry.desc))

theorem functionType_valid (types : List types.FuncType) (idx : U32) :
    Functype_ok (functionType types idx) := by
  cases he : types[idx.val]? with
  | none => simp only [functionType, he, Option.map_none, Option.getD_none]; constructor
  | some ft => simpa [functionType, he] using ModuleTranslation.funcType_valid ft

theorem importType_wf (types : List types.FuncType) (desc : module.ImportDesc) :
    wf_externtype (importType types desc) := by
  cases desc with
  | Func idx => constructor
  | Global gt => constructor
  | Table tt => exact .externtype_case_2 _ (EnvTranslation.tableType_wf tt)
  | Memory mt => exact .externtype_case_3 _ (EnvTranslation.memType_wf mt)

theorem import_type_valid {env : module.Env} {tables memories entry}
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

theorem import_typed {env : module.Env} {tables memories entry}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (he : entry ∈ env.imports.val)
    (hmod : wf_name (ModuleBinary.nameOfBytes entry.module.val))
    (hn : wf_name (ModuleBinary.nameOfBytes entry.name.val))
    (C : context) (hC : wf_context C) :
    Import_ok C (importDecl env.types.val (ModuleEnv.rawImport entry))
      (importType env.types.val entry.desc) := by
  exact .mk_Import_ok C _ _ _ (import_type_valid hc hv he) hC
    (.import_case_0 _ _ _ hmod hn (importType_wf _ _))

theorem start_typed {env : module.Env} (hv : ModuleEnv.Valid env) (idx : U32)
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
