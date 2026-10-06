import Itasca.ModuleProfile

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- Index spaces are derived from the independent decoded module, including
imports in their original order, rather than from validator caches. -/
def contextOf (raw : ModuleBinary.Module) : context :=
  let imports := raw.imports.map (fun e => importType raw.types e.desc)
  ⟨raw.types.map EnvTranslation.funcType,
    ModuleTranslation.funcs imports ++ raw.functions.map (functionType raw.types),
    ModuleTranslation.globals imports ++ raw.globals.map (fun g => Translate.globalType g.gtype),
    ModuleTranslation.tables imports ++ raw.tables.map EnvTranslation.tableType,
    ModuleTranslation.mems imports ++ raw.memories.map EnvTranslation.memType,
    List.replicate raw.elements.length .FUNCREF,
    List.replicate raw.data.length .OK, [], [], none⟩

theorem contextOf_fromEnv {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) :
    contextOf (fromEnv env tables memories codes segments) =
      moduleContext env env.elements.val.length segments.length := by
  symm
  simpa [contextOf, fromEnv, importTypes, ModuleEnv.rawImport, List.map_map, Function.comp_def]
    using moduleContext_eq hc env.elements.val.length segments.length

theorem import_types_resolved {env entries xts}
    (h : List.Forall₂ (ModuleExternals.ImportResolves env) entries xts) :
    xts.map ModuleExternals.externalType = entries.map (fun e => importType env.types.val e.desc) := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp [importType_resolved hp, ih]

/-- Exact successful results of both public type accessors are associated with
the independently elaborated module. `List.Forall₂` preserves export count. -/
def AccessorTypes (env : module.Env) (raw : ModuleBinary.Module) : Prop :=
  ∃ imports exports,
    module.import_types env = .ok (.Ok imports) ∧
    module.export_types env = .ok (.Ok exports) ∧
    imports.val.map ModuleExternals.externalType = raw.imports.map (fun e => importType raw.types e.desc) ∧
    List.Forall₂ (Export_ok (contextOf raw)) (raw.exports.map exportDecl)
      (exports.val.map ModuleExternals.externalType)

theorem accessorTypes {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (hn : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val)) :
    AccessorTypes env (fromEnv env tables memories codes segments) := by
  obtain ⟨ixts, hi⟩ := hc.imports_resolve
  obtain ⟨exts, he⟩ := hv.exports_resolve
  obtain ⟨ir, hir, imports, rfl, hiEq⟩ := WP.spec_imp_exists (module.import_types.resolved env ixts hi)
  obtain ⟨er, her, exports, rfl, heEq⟩ := WP.spec_imp_exists (module.export_types.resolved env exts he)
  refine ⟨imports, exports, hir, her, ?_, ?_⟩
  · simpa [hiEq, fromEnv, ModuleEnv.rawImport, List.map_map, Function.comp_def] using import_types_resolved hi
  · rw [heEq, contextOf_fromEnv hc]
    simpa [fromEnv, List.map_map, Function.comp_def] using
      exports_typed he hn _ (moduleContext_matches env env.elements.val.length segments.length)

/-- Returned declarations and data segments are exactly the independently
decoded module's declarations; merged runtime spaces retain their cache proof. -/
def Matches (env : module.Env) (tail : module.Tail) (raw : ModuleBinary.Module) : Prop :=
  raw = fromEnv env raw.tables raw.memories raw.codes tail.data.val ∧
    ModuleEnv.Cache env raw.tables raw.memories

theorem matches_fromEnv {env tables memories codes} (tail : module.Tail)
    (hc : ModuleEnv.Cache env tables memories) :
    Matches env tail (fromEnv env tables memories codes tail.data.val) := ⟨rfl, hc⟩

end Itasca.ModuleElaboration
