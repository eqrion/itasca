import Exec.Spec.Allocation
namespace Itasca.Runtime.Spec
open SpecExt

def allocationStore (s : store) (inst : moduleinst) (functions : List func)
    (globals : List globalinst) (tables : List tabletype) (memories : List memtype)
    (elements : List eleminst) (datas : List datainst) : store :=
  ⟨s.FUNCS ++ functions.map (allocationFunction inst), s.GLOBALS ++ globals,
    s.TABLES ++ tables.map allocationTable, s.MEMS ++ memories.map allocationMemory,
    s.ELEMS ++ elements, s.DATAS ++ datas⟩

private theorem store_parts {s : store} (wf : wf_store s) :
    Forall wf_funcinst s.FUNCS ∧ Forall wf_globalinst s.GLOBALS ∧ Forall wf_tableinst s.TABLES ∧
      Forall wf_meminst s.MEMS ∧ Forall wf_datainst s.DATAS := by
  cases wf; exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption⟩

/-- Concrete list allocation proves the generated whole-module allocator.
The only retained allocation-side evidence is syntax, index bounds, the exact
published module layout, and the independently checked export resolutions. -/
theorem allocate_module (s : store) (source : module) (externals : List externaddr)
    (inst : moduleinst) (types : List functype) (imports : List «import») (functions : List func)
    (globals : List globalinst) (tables : List tabletype) (memories : List memtype)
    (elements : List eleminst) (datas : List datainst)
    (globalExpressions : List expr) (elementExpressions : List (List expr))
    (elementModes : List elemmode) (dataModes : List datamode) (start : Option start)
    (exports : List «export») (exportInstances : List exportinst)
    (importedFunctions importedGlobals importedTables importedMemories : List Nat)
    (sourceEq : source = .MODULE (types.map type.TYPE) imports functions
      (Map₂ (fun expression ty => global.GLOBAL ty expression) globalExpressions (globals.map globalinst.TYPE))
      (tables.map table.TABLE) (memories.map mem.MEMORY)
      (Map₃ (fun mode expressions ty => elem.ELEM ty expressions mode)
        elementModes elementExpressions (elements.map eleminst.TYPE))
      (Map₂ data.DATA (datas.map datainst.BYTES) dataModes) start exports)
    (layout : inst = ⟨types,
      importedFunctions ++ List.range' s.FUNCS.length functions.length,
      importedGlobals ++ List.range' s.GLOBALS.length globals.length,
      importedTables ++ List.range' s.TABLES.length tables.length,
      importedMemories ++ List.range' s.MEMS.length memories.length,
      List.range' s.ELEMS.length elements.length, List.range' s.DATAS.length datas.length, exportInstances⟩)
    (importFunctions : fun_funcs externals importedFunctions)
    (importGlobals : fun_globals externals importedGlobals)
    (importTables : fun_tables externals importedTables)
    (importMemories : fun_mems externals importedMemories)
    (resolvedExports : List.Forall₂ (fun ex allocated => fun_instexport inst.FUNCS inst.GLOBALS inst.TABLES inst.MEMS ex allocated)
      exports exportInstances)
    (storeWf : wf_store s) (sourceWf : wf_module source) (instanceWf : wf_moduleinst inst)
    (functionsWf : Forall wf_func functions)
    (functionBounds : ∀ function ∈ functions, allocationFunctionIndex function < inst.TYPES.length)
    (globalsWf : Forall wf_globalinst globals) (tablesWf : Forall wf_tabletype tables)
    (memoriesWf : Forall wf_memtype memories) (datasWf : Forall wf_datainst datas) :
    fun_allocmodule s source externals (globals.map globalinst.VALUE) (elements.map eleminst.REFS)
      (allocationStore s inst functions globals tables memories elements datas, inst) := by
  let s1 := {s with FUNCS := s.FUNCS ++ functions.map (allocationFunction inst)}
  let s2 := {s1 with GLOBALS := s.GLOBALS ++ globals}
  let s3 := {s2 with TABLES := s.TABLES ++ tables.map allocationTable}
  let s4 := {s3 with MEMS := s.MEMS ++ memories.map allocationMemory}
  let s5 := {s4 with ELEMS := s.ELEMS ++ elements}
  let s6 := allocationStore s inst functions globals tables memories elements datas
  have f := allocate_functions s inst functions instanceWf functionsWf functionBounds
  have g := allocate_globals s1 globals globalsWf
  have t := allocate_tables s2 tables tablesWf
  have m := allocate_memories s3 memories memoriesWf
  have e := allocate_elements s4 elements
  have d := allocate_datas s5 datas datasWf
  obtain ⟨oldFunctions, oldGlobals, oldTables, oldMemories, oldDatas⟩ := store_parts storeWf
  have newFunctions : Forall wf_funcinst (functions.map (allocationFunction inst)) := by
    intro value member
    obtain ⟨function, present, rfl⟩ := List.mem_map.mp member
    exact allocation_function_wf inst function instanceWf (functionsWf function present)
  have newTables : Forall wf_tableinst (tables.map allocationTable) := by
    intro value member
    obtain ⟨ty, present, rfl⟩ := List.mem_map.mp member
    cases ty with | mk_tabletype limits rt =>
      cases limits with | mk_limits minimum maximum =>
        cases minimum
        exact .tableinst_case_ _ _ (tablesWf _ present)
  have newMemories : Forall wf_meminst (memories.map allocationMemory) := by
    intro value member
    obtain ⟨ty, present, rfl⟩ := List.mem_map.mp member
    cases ty with | PAGE limits =>
      cases limits with | mk_limits minimum maximum =>
        cases minimum
        constructor
        · exact memoriesWf _ present
        · intro value member
          have same := (List.mem_replicate.mp member).2
          rw [same]; constructor; norm_num
  have wf1 : wf_store s1 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) oldGlobals oldTables oldMemories oldDatas
  have wf2 : wf_store s2 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) oldTables oldMemories oldDatas
  have wf3 : wf_store s3 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) oldMemories oldDatas
  have wf4 : wf_store s4 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) oldDatas
  have wf5 : wf_store s5 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) oldDatas
  have wf6 : wf_store s6 := .store_case_ _ _ _ _ _ _ (forall_append oldFunctions newFunctions) (forall_append oldGlobals globalsWf) (forall_append oldTables newTables) (forall_append oldMemories newMemories) (forall_append oldDatas datasWf)
  have exportsResolved : Forall₂ (fun allocated ex => fun_instexport
      (importedFunctions ++ List.range' s.FUNCS.length functions.length)
      (importedGlobals ++ List.range' s.GLOBALS.length globals.length)
      (importedTables ++ List.range' s.TABLES.length tables.length)
      (importedMemories ++ List.range' s.MEMS.length memories.length) ex allocated) exportInstances exports := by
    intro pair member
    have proof := List.forall₂_zip resolvedExports.flip member
    simpa only [layout] using proof
  refine fun_allocmodule.fun_allocmodule_case_0 s source externals (globals.map globalinst.VALUE)
    (elements.map eleminst.REFS) s6 inst types imports functions.length functions globals.length
    globalExpressions (globals.map globalinst.TYPE) tables.length tables memories.length memories
    elements.length elementModes elementExpressions (elements.map eleminst.TYPE) datas.length
    (datas.map datainst.BYTES) dataModes start exports s1 s2 s3 s4 s5
    importedFunctions importedGlobals importedTables importedMemories
    (List.range' s.FUNCS.length functions.length) (List.range' s.GLOBALS.length globals.length)
    (List.range' s.TABLES.length tables.length) (List.range' s.MEMS.length memories.length)
    (List.range' s.ELEMS.length elements.length) (List.range' s.DATAS.length datas.length)
    exportInstances _ _ _ _ _ _ exportInstances importedMemories importedTables importedGlobals importedFunctions
    d e m t g f resolvedExports.length_eq.symm exportsResolved importMemories importTables importGlobals importFunctions
    sourceEq rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl layout rfl rfl rfl rfl rfl rfl
    wf6 instanceWf wf1 wf2 wf3 wf4 wf5 ?_ ?_
  all_goals first
    | exact List.range'_eq_map_range
    | simpa only [← sourceEq, Map] using sourceWf
    | simpa only [← layout] using instanceWf
end Itasca.Runtime.Spec
