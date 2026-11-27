import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Module.Const.Parser
import Itasca.Spec.Typing
import Itasca.Module.Readers.ImportTypes
import Itasca.Module.Env.References
import Itasca.Module.Elab.Translation
import Mathlib.Data.List.Forall2
import Itasca.Module.Elab.SegmentTyping

open WebAssembly

/-! Semantic invariants of the metadata decoded before the code section. -/

open Aeneas Aeneas.Std

namespace Itasca.Module.Externals

/-- The external type `xt` is what import `imp` denotes, found by index-space lookup rather than by
running the accessor. -/
def ImportResolves (env : metadata.CodeMetadata) (imp : Binary.Import) (xt : wasm_types.ExternType) : Prop :=
  match imp.desc with
  | .Func idx => ∃ hi : idx.val < env.types.val.length, xt = .Func env.types.val[idx.val]
  | .Table tt => xt = .Table tt
  | .Memory mt => xt = .Memory mt
  | .Global gt => xt = .Global gt

end Itasca.Module.Externals

namespace Itasca.Module.Environment

/-- The semantic checks that are stored in, or derivable from, the environment in the module.
Byte-format evidence is tracked separately. -/
structure Valid (env : metadata.ModuleMetadata metadata.CodeMetadata) : Prop where
  types : ∀ ft ∈ env.code.types.val, CodeEntry.FuncTypeWithinLimits ft
  funcs : ∀ d ∈ env.code.funcs.val, d.type_index.val < env.code.types.val.length
  tables : ∀ d ∈ env.code.tables.val, Module.Translation.LimitsValid d.ty.limits (2 ^ 32 - 1)
  memories : ∀ d ∈ env.code.memories.val, Module.Translation.LimitsValid d.ty.limits (2 ^ 16)
  memoryCount : env.code.memories.val.length ≤ 1
  globals : ∀ g ∈ env.code.globals.val, ∀ init, g.init = some init →
    Module.Constants.Valid env.code init g.gtype.valtype
  imports : ∀ entry ∈ env.imports.val, Binary.Utf8 entry.module.val ∧ Binary.Utf8 entry.name.val
  exportNames : ∀ entry ∈ env.exports.val, Binary.Utf8 entry.name.val
  distinctExports : (env.exports.val.map fun entry => entry.name.val).Nodup
  exports : ∀ entry ∈ env.exports.val, ∃ xt, Module.Externals.ExportResolves env.code entry xt
  start : ∀ idx, env.code.start = some idx →
    ∃ ft, env.code.externalTypeAt (.Func idx) = some (.Func ft) ∧
      ft.params.val = [] ∧ ft.results.val = []
  elements : ∀ entry ∈ env.elements.val, Module.Segments.elementValid env.code entry
  references : Module.References.Coherent env

/-- Every retained vector and import counter is bounded by the input consumed. -/
structure Bounded (env : metadata.ModuleMetadata metadata.CodeMetadata) (pos : Nat) : Prop where
  types : env.code.types.val.length ≤ pos
  imports : env.imports.val.length ≤ pos
  globals : env.code.globals.val.length ≤ pos
  exports : env.exports.val.length ≤ pos
  elements : env.elements.val.length ≤ pos
  elementTypes : env.code.elem_segment_types.val.length ≤ pos
  funcs : env.code.funcs.val.length ≤ pos
  tables : env.code.tables.val.length ≤ pos
  memories : env.code.memories.val.length ≤ pos
  numFuncs : env.code.num_imported_funcs.val ≤ pos
  numGlobals : env.code.num_imported_globals.val ≤ pos

theorem Bounded.mono {env pos next} (h : Bounded env pos) (hle : pos ≤ next) :
    Bounded env next := by
  cases h
  constructor <;> omega

theorem Cache.global_prefix {env imports functions globals tables memories}
    (h : Cache env imports functions globals tables memories) :
    (env.globals.val.take env.num_imported_globals.val).map metadata.Global.gtype = importedGlobals imports := by
  have types := congrArg (List.map Prod.fst) h.globalEntries
  simp only [List.map_append, List.map_map, Function.comp_def, List.map_id_fun, List.map_id] at types
  simp [List.map_take, h.numGlobals, types]

theorem Valid.environment_within_limits {env} (hv : Valid env) : CodeEntry.EnvironmentWithinLimits env.code :=
  ⟨hv.types, hv.funcs⟩

theorem Cache.import_indices {env imports functions globals tables memories}
    (h : Cache env imports functions globals tables memories)
    (valid : ∀ d ∈ env.funcs.val, d.type_index.val < env.types.val.length) :
    ∀ idx ∈ importedFuncs imports, idx.val < env.types.val.length := by
  intro idx hi
  have hm : idx ∈ env.funcs.val.map metadata.FuncDesc.type_index := h.funcs ▸ List.mem_append_left _ hi
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
  exact valid d hd

/-- Every import of a cached environment has a resolved external type. -/
theorem Cache.imports_resolve {env imports functions globals tables memories}
    (h : Cache env imports functions globals tables memories)
    (valid : ∀ d ∈ env.funcs.val, d.type_index.val < env.types.val.length) :
    ∃ xts, List.Forall₂ (Module.Externals.ImportResolves env) imports xts := by
  have hb := h.import_indices valid
  clear h
  generalize imports = entries at hb ⊢
  induction entries with
  | nil => exact ⟨[], .nil⟩
  | cons entry entries ih =>
    have hb' : ∀ idx ∈ importedFuncs entries, idx.val < env.types.val.length := by
      intro idx hi
      apply hb idx
      cases entry.desc <;> simp_all [importedFuncs]
    obtain ⟨rest, hr⟩ := ih hb'
    cases hd : entry.desc with
    | Func idx =>
      have hi : idx.val < env.types.val.length := hb idx (by simp [importedFuncs, hd])
      exact ⟨.Func env.types.val[idx.val] :: rest, .cons (by simpa [Module.Externals.ImportResolves, hd] using (show ∃ hj : idx.val < env.types.val.length, (wasm_types.ExternType.Func env.types.val[idx.val]) = .Func env.types.val[idx.val] from ⟨hi, rfl⟩)) hr⟩
    | Table tt => exact ⟨.Table tt :: rest, .cons (by simp [Module.Externals.ImportResolves, hd]) hr⟩
    | Memory mt => exact ⟨.Memory mt :: rest, .cons (by simp [Module.Externals.ImportResolves, hd]) hr⟩
    | Global gt => exact ⟨.Global gt :: rest, .cons (by simp [Module.Externals.ImportResolves, hd]) hr⟩

theorem Valid.exports_resolve {env} (h : Valid env) :
    ∃ xts, List.Forall₂ (Module.Externals.ExportResolves env.code) env.exports.val xts := by
  have he := h.exports
  generalize env.exports.val = entries at he ⊢
  induction entries with
  | nil => exact ⟨[], .nil⟩
  | cons entry entries ih =>
    obtain ⟨xt, ht⟩ := he entry (by simp)
    obtain ⟨xts, hrest⟩ := ih (by intro entry hm; exact he entry (by simp [hm]))
    exact ⟨xt :: xts, .cons ht hrest⟩

end Itasca.Module.Environment

namespace Itasca

/-- Empty prefix metadata has valid index spaces and zero cursor bounds. -/
@[step] theorem metadata.ModuleMetadataCodeMetadata.new.spec :
    metadata.ModuleMetadataCodeMetadata.new ⦃ env =>
      Module.Environment.Cache env.code [] [] [] [] [] ∧
      Module.Environment.Valid env ∧ Module.Environment.Bounded env 0 ⦄ := by
  simp only [metadata.ModuleMetadataCodeMetadata.new, metadata.CodeMetadata.new, bind_ok, WP.spec_ok]
  constructor
  · constructor <;> simp [Module.Environment.importedFuncs, Module.Environment.importedGlobals,
      Module.Environment.importedTables, Module.Environment.importedMems]
  · constructor
    · constructor <;> simp [Module.References.Coherent, Module.References.collected,
        Translation.Environment.declaredReferences]
    · constructor <;> simp

end Itasca
