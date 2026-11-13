import Itasca.Module.Elab.Profile

/-!
Sections, each formerly its own module: Metadata, TypingInversion.
-/

/-! ## Metadata -/

section

/-!
# Returned metadata

`Matches` says the environment and tail the validator returns describe exactly a raw module, and
`AccessorTypes` says the results of `metadata.import_types` and `metadata.export_types` agree with the
elaborated module's import types and typed exports. `contextOf` is the module context computed from
the raw module alone, and `accessorTypes` and `matches_fromEnv` establish these properties for a
valid cached environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The module typing context computed from the independently decoded module. Index spaces list
imports in import order and do not depend on validator caches. -/
def contextOf (raw : ModuleBinary.Module) : context :=
  let imports := raw.imports.map (fun e => importType raw.types e.desc)
  ⟨raw.types.map EnvTranslation.funcType,
    ModuleTranslation.funcs imports ++ raw.functions.map (functionType raw.types),
    ModuleTranslation.globals imports ++ raw.globals.map (fun g => Translate.globalType g.gtype),
    ModuleTranslation.tables imports ++ raw.tables.map EnvTranslation.tableType,
    ModuleTranslation.mems imports ++ raw.memories.map EnvTranslation.memType,
    raw.elements.map (fun entry => Translate.referenceType entry.elem),
    List.replicate raw.data.length .OK, [], [], none⟩

/-- For a cached environment, the raw module's own context is `moduleContext`. -/
theorem contextOf_fromEnv {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) :
    contextOf (fromEnv env tables memories codes segments) =
      moduleContext env (EnvTranslation.elementTypes env) segments.length := by
  symm
  simpa [contextOf, fromEnv, importTypes, ModuleEnv.rawImport, ModuleEnv.rawElement,
    EnvTranslation.elementTypes, List.map_map, Function.comp_def]
    using moduleContext_eq hc (EnvTranslation.elementTypes env) segments.length

/-- Resolved import types translate to the elaborated import types. -/
theorem import_types_resolved {env entries xts}
    (h : List.Forall₂ (ModuleExternals.ImportResolves env) entries xts) :
    xts.map ModuleExternals.externalType = entries.map (fun e => importType env.types.val e.desc) := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp [importType_resolved hp, ih]

/-- Both type accessors succeed on `env`, and their results match the elaborated module: the import
types are equal, and the exports are typed by `Export_ok` pointwise, which preserves the export
count. -/
def AccessorTypes (env : metadata.Env) (raw : ModuleBinary.Module) : Prop :=
  ∃ imports exports,
    metadata.import_types env = .ok (.Ok imports) ∧
    metadata.export_types env = .ok (.Ok exports) ∧
    imports.val.map ModuleExternals.externalType = raw.imports.map (fun e => importType raw.types e.desc) ∧
    List.Forall₂ (Export_ok (contextOf raw)) (raw.exports.map exportDecl)
      (exports.val.map ModuleExternals.externalType)

/-- A valid cached environment with well-formed export names has `AccessorTypes` for the module it
describes. -/
theorem accessorTypes {env tables memories codes segments}
    (hc : ModuleEnv.Cache env tables memories) (hv : ModuleEnv.Valid env)
    (hn : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val)) :
    AccessorTypes env (fromEnv env tables memories codes segments) := by
  obtain ⟨ixts, hi⟩ := hc.imports_resolve
  obtain ⟨exts, he⟩ := hv.exports_resolve
  obtain ⟨ir, hir, imports, rfl, hiEq⟩ := WP.spec_imp_exists (metadata.import_types.resolved env ixts hi)
  obtain ⟨er, her, exports, rfl, heEq⟩ := WP.spec_imp_exists (metadata.export_types.resolved env exts he)
  refine ⟨imports, exports, hir, her, ?_, ?_⟩
  · simpa [hiEq, fromEnv, ModuleEnv.rawImport, List.map_map, Function.comp_def] using import_types_resolved hi
  · rw [heEq, contextOf_fromEnv hc]
    simpa [fromEnv, List.map_map, Function.comp_def] using
      exports_typed he hn _ (moduleContext_matches env (EnvTranslation.elementTypes env) segments.length)

/-- The returned declarations and data segments are exactly the independently decoded module's
declarations, and the merged index spaces satisfy `ModuleEnv.Cache`. -/
def Matches (env : metadata.Env) (tail : metadata.Tail) (raw : ModuleBinary.Module) : Prop :=
  raw = fromEnv env raw.tables raw.memories raw.codes tail.data.val ∧
    ModuleEnv.Cache env raw.tables raw.memories

/-- A cached environment and tail match the module `fromEnv` builds from them. -/
theorem matches_fromEnv {env tables memories codes} (tail : metadata.Tail)
    (hc : ModuleEnv.Cache env tables memories) :
    Matches env tail (fromEnv env tables memories codes tail.data.val) := ⟨rfl, hc⟩

end Itasca.ModuleElaboration

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

namespace Itasca.ModuleElaboration

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
def initializerContextOf (raw : ModuleBinary.Module) : context :=
  { contextOf raw with
    GLOBALS := ModuleTranslation.globals (raw.imports.map (fun e => importType raw.types e.desc))
    ELEMS := [], DATAS := [] }

/-- The canonical section judgments recovered from generated module typing. The contexts are
computed from the independent raw module and not from parser output. -/
structure SectionsTyped (raw : ModuleBinary.Module) : Prop where
  imports : ∀ e ∈ raw.imports, Externtype_ok (importType raw.types e.desc)
  globals : ∀ g ∈ raw.globals,
    Global_ok (initializerContextOf raw) (ModuleConstants.global g) (Translate.globalType g.gtype)
  tables : ∀ tt ∈ raw.tables, Tabletype_ok (EnvTranslation.tableType tt)
  memories : ∀ mt ∈ raw.memories, Memtype_ok (EnvTranslation.memType mt)
  elements : ∀ e ∈ raw.elements,
    Elem_ok (initializerContextOf raw) (element e) (Translate.referenceType e.elem)
  data : ∀ d ∈ raw.data, Data_ok (initializerContextOf raw) (ModuleData.translate d)
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
    (hC : C.TYPES = ts.map EnvTranslation.funcType) : ft = functionType ts idx := by
  have hi := func_index_bound h
  have he := func_type_lookup h
  have hidx : idx.val < ts.length := by simpa [CodeEntry.function, hC, proj_uN_0] using hi
  rw [functionType_lookup hidx]
  change ft = C.TYPES[idx.val]! at he
  rw [hC, getElem!_pos _ _ (by simpa using hidx), List.getElem_map] at he
  exact he

/-- Typed functions in a context with translated types determine the function types of their type
indices, and each entry is typed at its own type. -/
theorem function_lists_of_typing {C : context} {ts : List wasm_types.FuncType} {indices codes fts}
    (hn : indices.length = codes.length)
    (h : List.Forall₂ (fun ft f => Func_ok C f ft) fts (List.zipWith CodeEntry.function indices codes))
    (hC : C.TYPES = ts.map EnvTranslation.funcType) :
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
theorem sections_of_typing {raw : ModuleBinary.Module}
    (he : Elaborates raw (moduleOf raw)) (h : Module_ok (moduleOf raw)) : SectionsTyped raw := by
  unfold moduleOf at h
  cases h
  rename_i n fts ixt C' gts tts mts rts C ftdefs xts ifts igts itts imts v3 v2 v1 v0
    hmproj htproj hgproj hfproj hmemcap hC hC' hif hig hit him hwi hwC' hwC hwx hwtab hwmem
    hwimport hwfull hwinit htylen htys himplen himps hfunlen hfuns hgloblen hglobs
    htablen htabs hmemlen hmems helemlen helems hdatas hn hstarts hexplen hexps hwmodule
  have htys' := forall₂_of_generated htylen htys
  have hfts : fts = raw.types.map EnvTranslation.funcType :=
    eq_map_left htys' (fun _ _ hp => by cases hp; rfl)
  have himps' := forall₂_of_generated himplen himps
  have hixt : ixt = raw.imports.map (fun e => importType raw.types e.desc) :=
    eq_map_right himps' (fun _ _ hp => by cases hp; rfl)
  have hglobs' := forall₂_of_generated hgloblen hglobs
  have hgts : gts = raw.globals.map (fun g => Translate.globalType g.gtype) :=
    eq_map_right hglobs' (fun _ _ hp => by cases hp; rfl)
  have htabs' := forall₂_of_generated htablen htabs
  have htts : tts = raw.tables.map EnvTranslation.tableType :=
    eq_map_right htabs' (fun _ _ hp => by cases hp; rfl)
  have hmems' := forall₂_of_generated hmemlen hmems
  have hmts : mts = raw.memories.map EnvTranslation.memType :=
    eq_map_right hmems' (fun _ _ hp => by cases hp; rfl)
  have helems' := forall₂_of_generated helemlen helems
  have hrts : rts = raw.elements.map (fun entry => Translate.referenceType entry.elem) :=
    eq_map_right helems' (fun _ _ hp => by cases hp; rfl)
  have hfuns' := forall₂_of_generated hfunlen hfuns
  have hCtypes : C.TYPES = raw.types.map EnvTranslation.funcType := by rw [hC]; exact hfts
  obtain ⟨hftdefs, hfunctions⟩ := function_lists_of_typing he.code_count hfuns' hCtypes
  have hifs : ifts = ModuleTranslation.funcs ixt := hif.trans (ModuleTranslation.funcs_unique hfproj)
  have higs : igts = ModuleTranslation.globals ixt := hig.trans (ModuleTranslation.globals_unique hgproj)
  have hits : itts = ModuleTranslation.tables ixt := hit.trans (ModuleTranslation.tables_unique htproj)
  have hims : imts = ModuleTranslation.mems ixt := him.trans (ModuleTranslation.mems_unique hmproj)
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

end Itasca.ModuleElaboration

end
