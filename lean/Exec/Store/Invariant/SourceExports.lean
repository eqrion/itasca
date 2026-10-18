import Exec.Store.Invariant.SourceSyntax
import Itasca.Module.Env.Basic
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- Runtime export decoding resolves the same namespace entry as the generated
module allocator, using the validated index and the completed instance map. -/
theorem export_source {M : Type} (store : runtime.store.Store M) (inst : runtime.store.Instance)
    (entry : Itasca.module.Export) (ty : types.ExternType)
    (shape : InstanceShape store inst)
    (resolved : ModuleExternals.ExportResolves inst.module.module.env entry ty)
    (nameWf : wf_name (decodeName entry.name.val)) :
    fun_instexport (decodeInstance store inst).FUNCS (decodeInstance store inst).GLOBALS
      (decodeInstance store inst).TABLES (decodeInstance store inst).MEMS
      (ModuleElaboration.exportDecl (ModuleEnv.rawExport entry)) (decodeExport inst entry) := by
  obtain ⟨_, functionCount, tableCount, memoryCount, globalCount, _⟩ := shape
  cases desc : entry.desc with
  | Func index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.funcs.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.funcs.length
      rw [functionCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_0
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decodeName_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source
  | Global index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.globals.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.globals.length
      rw [globalCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_1
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decodeName_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source
  | Table index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.tables.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.tables.length
      rw [tableCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_2
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decodeName_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source
  | Memory index =>
    simp only [ModuleExternals.ExportResolves, desc] at resolved
    obtain ⟨bound, _⟩ := resolved
    have mapped : index.val < (inst.memories.val.map (fun address => address.index.val)).length := by
      simp only [List.length_map]
      change index.val < inst.memories.length
      rw [memoryCount]
      exact bound
    have source := fun_instexport.fun_instexport_case_3
      (inst.funcs.val.map (fun address => address.index.val))
      (inst.globals.val.map (fun address => address.index.val))
      (inst.tables.val.map (fun address => address.index.val))
      (inst.memories.val.map (fun address => address.index.val))
      (decodeName entry.name.val) (.mk_uN index.val) (by simpa [proj_uN_0] using mapped) (by simpa [proj_uN_0] using mapped) (.exportinst_case_ _ _ nameWf)
    simpa only [decodeInstance, ModuleElaboration.exportDecl, ModuleEnv.rawExport,
      ModuleElaboration.exportIndex, decodeExport, desc, ← decodeName_source,
      List.getElem!_eq_getElem?_getD, List.getD, proj_uN_0,
      List.getElem?_eq_getElem mapped, Option.getD_some] using source

/-- All source-ordered exports satisfy the generated allocator's resolutions. -/
theorem exports_source {M : Type} (store : runtime.store.Store M) (inst : runtime.store.Instance)
    (shape : InstanceShape store inst)
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
    (code : CodeInterpretation) (instanceIndex : Nat) (sourceSyntax : InstanceSyntax code instanceIndex inst) :
    List.Forall₂ (fun source allocated => fun_instexport
      (decodeInstance store inst).FUNCS (decodeInstance store inst).GLOBALS
      (decodeInstance store inst).TABLES (decodeInstance store inst).MEMS source allocated)
      (inst.module.module.env.exports.val.map (fun entry => ModuleElaboration.exportDecl (ModuleEnv.rawExport entry)))
      (inst.module.module.env.exports.val.map (decodeExport inst)) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro entry member
  obtain ⟨ty, resolved⟩ := valid.exports entry member
  exact export_source store inst entry ty shape resolved (sourceSyntax.exportNames entry member)

/-- The exact canonical source export list resolves to the decoded instance's
export records. -/
theorem exports_source_raw {M : Type} (store : runtime.store.Store M) (inst : runtime.store.Instance)
    (shape : InstanceShape store inst)
    (valid : Itasca.ModuleEnv.Valid inst.module.module.env inst.module.profile)
    (code : CodeInterpretation) (instanceIndex : Nat) (sourceSyntax : InstanceSyntax code instanceIndex inst)
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw) :
    List.Forall₂ (fun source allocated => fun_instexport
      (decodeInstance store inst).FUNCS (decodeInstance store inst).GLOBALS
      (decodeInstance store inst).TABLES (decodeInstance store inst).MEMS source allocated)
      (raw.exports.map ModuleElaboration.exportDecl) (decodeInstance store inst).EXPORTS := by
  have exports := congrArg ModuleBinary.Module.exports matched.1
  simp only [ModuleElaboration.fromEnv] at exports
  have resolved := exports_source store inst shape valid code instanceIndex sourceSyntax
  rw [exports]
  simpa only [List.map_map, Function.comp_def, decodeInstance] using resolved
end Exec.Store
