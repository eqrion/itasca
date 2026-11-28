import Itasca.Module.Elab.ValidatedSections

open WebAssembly

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

`AccessorTypes` relates both shared-module accessors to the import and export types
of the independently elaborated module. `Matches` relates the retained metadata,
including descriptor flags and final data segments, to that same module.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Elaboration

/-- For a cached environment, the raw module's own context is `moduleContext`. -/
theorem context_of_from_env {env decls codes segments}
    (rep : Module.Environment.Represents env decls) :
    contextOf (fromEnv env decls codes segments) =
      moduleContext env.code (Translation.Environment.elementTypes env.code) segments.length := by
  symm
  simpa [contextOf, fromEnv, importTypes, Module.Environment.rawElement, rep.elementTypes, rep.elements,
    Translation.Environment.elementTypes, List.map_map, Function.comp_def]
    using module_context_eq rep.cache (Translation.Environment.elementTypes env.code) segments.length

/-- Resolved import types translate to the elaborated import types. -/
theorem import_types_resolved {env entries xts}
    (h : List.Forall₂ (Module.Externals.ImportResolves env) entries xts) :
    xts.map Module.Externals.externalType = entries.map (fun e => importType env.types.val e.desc) := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp [import_type_resolved hp, ih]

/-- A valid cached environment with well-formed export names has `AccessorTypes` for the module it
describes. -/
theorem accessor_types {env decls codes segments} (data : alloc.vec.Vec metadata.Data)
    (rep : Module.Environment.Represents env decls) (hv : Module.Environment.Valid env)
    (bound : decls.imports.length ≤ U32.max)
    (hn : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val)) :
    AccessorTypes {env with data := data} (fromEnv env decls codes segments) := by
  obtain ⟨ixts, hi⟩ := rep.cache.imports_resolve hv.funcs
  obtain ⟨exts, he⟩ := hv.exports_resolve
  obtain ⟨ir, hir, imports, rfl, hiEq⟩ := WP.spec_imp_exists
    (metadata.ModuleMetadataArcCodeMetadata.import_types.resolved {env with data := data} ixts (rep.ordered_imports hi bound))
  obtain ⟨er, her, exports, rfl, heEq⟩ := WP.spec_imp_exists (metadata.ModuleMetadataArcCodeMetadata.export_types.resolved {env with data := data} exts he)
  refine ⟨imports, exports, hir, her, ?_, ?_⟩
  · rw [hiEq]
    exact import_types_resolved hi
  · rw [heEq, context_of_from_env rep]
    simpa [fromEnv, List.map_map, Function.comp_def] using
      exports_typed he hn _ (module_context_matches env.code (Translation.Environment.elementTypes env.code) segments.length)

/-- Installing the validated data segments completes the module described by the prefix. -/
theorem matches_from_env {env decls codes} (data : alloc.vec.Vec metadata.Data)
    (rep : Module.Environment.Represents env decls) (valid : Module.Environment.Valid env)
    (flags : Module.Environment.DescriptorFlags env)
    (segments : ∀ entry ∈ data.val, Module.Data.Valid env.code entry) :
    Matches { env with data := data } (fromEnv env decls codes data.val) := by
  refine ⟨rfl, rep.imports, rfl, rfl, rfl, ?_, rfl, rfl, rep.cache,
    Module.References.coherent_declared_iff (env := env) (codes := codes) rep valid.references valid.elements segments,
    ?_, ?_, ?_, ?_⟩
  · simpa [fromEnv, ← rep.elements] using rep.elementTypes
  · simpa [fromEnv, List.mem_map, Module.Environment.rawExport] using flags.eager
  · simpa [fromEnv, List.mem_map, Module.Environment.rawExport] using flags.tablesExported
  · simpa [fromEnv, List.mem_map, Module.Environment.rawExport] using flags.memoriesExported
  · simpa [fromEnv, List.mem_map, Module.Environment.rawExport] using flags.globalsExported

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
