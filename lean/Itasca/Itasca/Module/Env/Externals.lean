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

private theorem lookup_of_drop_cons {xs : List α} {f : α → β} {i : Nat} {b bs}
    (h : (xs.map f).drop i = b :: bs) :
    ∃ a, xs[i]? = some a ∧ f a = b := by
  have hd := congrArg List.head? h
  simpa [List.getElem?_map, Option.map_eq_some_iff] using hd

private theorem next_drop {xs : List α} {i : Nat} {x rest}
    (h : xs.drop i = x :: rest) : xs.drop (i + 1) = rest := by
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using congrArg (List.drop 1) h

open Module.Externals in
private theorem ordered_imports_from_positions {env entries types}
    (typed : List.Forall₂ (ImportResolves env) entries types)
    (records : List metadata.Import) (p : ImportPositions)
    (same : records.map (fun i => (i.module.val, i.name.val, i.kind)) = entries.map importRecord)
    (funcs : List U32)
    (hfuncs : (env.funcs.val.map metadata.FuncDesc.type_index).drop p.funcs.val = importedFuncs entries ++ funcs)
    (bfuncs : p.funcs.val + entries.length ≤ U32.max)
    (tables : List wasm_types.TableType)
    (htables : (env.tables.val.map metadata.TableDesc.ty).drop p.tables.val = importedTables entries ++ tables)
    (btables : p.tables.val + entries.length ≤ U32.max)
    (memories : List wasm_types.MemType)
    (hmemories : (env.memories.val.map metadata.MemoryDesc.ty).drop p.memories.val = importedMems entries ++ memories)
    (bmemories : p.memories.val + entries.length ≤ U32.max)
    (globals : List wasm_types.GlobalType)
    (hglobals : (env.globals.val.map metadata.Global.gtype).drop p.globals.val = importedGlobals entries ++ globals)
    (bglobals : p.globals.val + entries.length ≤ U32.max)
    : ImportTypes env p records types := by
  induction typed generalizing records p with
  | nil => cases records <;> simp_all [ImportTypes.nil]
  | @cons entry xt entries types head _ ih =>
    cases records with
    | nil => simp at same
    | cons record records =>
      obtain ⟨names, tail⟩ := List.cons.inj same
      have kind := congrArg (fun r : List U8 × List U8 × metadata.ImportKind => r.2.2) names
      simp only [List.length_cons] at bfuncs btables bmemories bglobals
      cases hd : entry.desc <;>
        simp [importRecord, hd] at kind <;>
        simp only [importedFuncs, importedTables, importedMems, importedGlobals, List.filterMap_cons,
          hd, List.cons_append] at hfuncs htables hmemories hglobals
      case Func ty =>
        obtain ⟨d, look, eq⟩ := lookup_of_drop_cons hfuncs
        let next := U32.ofNatCore (p.funcs.val + 1) (by scalar_tac)
        apply ImportTypes.cons (q := { p with funcs := next })
        · simp only [ImportResolves, hd] at head
          obtain ⟨bound, rfl⟩ := head
          simp [kind, ImportPositions.current, metadata.CodeMetadata.externalTypeAt, look, eq, List.getElem?_eq_getElem bound]
        · simp [kind, ImportPositions.Advances, next]
        · apply ih records _ tail <;> first
          | assumption
          | exact next_drop hfuncs
          | (simp only [next, U32.ofNatCore_val_eq]; omega)
      case Table ty =>
        obtain ⟨d, look, eq⟩ := lookup_of_drop_cons htables
        let next := U32.ofNatCore (p.tables.val + 1) (by scalar_tac)
        apply ImportTypes.cons (q := { p with tables := next })
        · simp only [ImportResolves, hd] at head
          simp [kind, ImportPositions.current, metadata.CodeMetadata.externalTypeAt, look, eq, head]
        · simp [kind, ImportPositions.Advances, next]
        · apply ih records _ tail <;> first
          | assumption
          | exact next_drop htables
          | (simp only [next, U32.ofNatCore_val_eq]; omega)
      case Memory ty =>
        obtain ⟨d, look, eq⟩ := lookup_of_drop_cons hmemories
        let next := U32.ofNatCore (p.memories.val + 1) (by scalar_tac)
        apply ImportTypes.cons (q := { p with memories := next })
        · simp only [ImportResolves, hd] at head
          simp [kind, ImportPositions.current, metadata.CodeMetadata.externalTypeAt, look, eq, head]
        · simp [kind, ImportPositions.Advances, next]
        · apply ih records _ tail <;> first
          | assumption
          | exact next_drop hmemories
          | (simp only [next, U32.ofNatCore_val_eq]; omega)
      case Global ty =>
        obtain ⟨d, look, eq⟩ := lookup_of_drop_cons hglobals
        let next := U32.ofNatCore (p.globals.val + 1) (by scalar_tac)
        apply ImportTypes.cons (q := { p with globals := next })
        · simp only [ImportResolves, hd] at head
          simp [kind, ImportPositions.current, metadata.CodeMetadata.externalTypeAt, look, eq, head]
        · simp [kind, ImportPositions.Advances, next]
        · apply ih records _ tail <;> first
          | assumption
          | exact next_drop hglobals
          | (simp only [next, U32.ofNatCore_val_eq]; omega)

/-- The reader visits the imported prefix of each descriptor space in declaration order. -/
theorem Represents.ordered_imports {env decls types} (rep : Represents env decls)
    (typed : List.Forall₂ (Module.Externals.ImportResolves env.code) decls.imports types)
    (bound : decls.imports.length ≤ U32.max) :
    Module.Externals.ImportTypes env.code ⟨0#u32, 0#u32, 0#u32, 0#u32⟩ env.imports.val types := by
  refine ordered_imports_from_positions typed _ _ rep.imports decls.functions rep.cache.funcs
    (by simpa using bound) decls.tables ?_ (by simpa using bound) decls.memories ?_
    (by simpa using bound) (decls.globals.map Binary.Global.gtype) ?_ (by simpa using bound)
  · simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) rep.cache.tableEntries
  · simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) rep.cache.memoryEntries
  · simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) rep.cache.globalEntries

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
