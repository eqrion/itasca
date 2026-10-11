import Itasca.Module.ModuleMetadata

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

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

def initializerContextOf (raw : ModuleBinary.Module) : context :=
  { contextOf raw with
    GLOBALS := ModuleTranslation.globals (raw.imports.map (fun e => importType raw.types e.desc))
    ELEMS := [], DATAS := [] }

/-- Canonical section judgments recovered from generated module typing. The
contexts are calculated from the independent raw module, not parser output. -/
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

theorem func_index_bound {C : context} {f ft} (h : Func_ok C f ft) :
    match f with | .FUNC idx _ _ => proj_uN_0 idx < C.TYPES.length := by
  cases h
  assumption

theorem func_type_lookup {C : context} {f ft} (h : Func_ok C f ft) :
    match f with | .FUNC idx _ _ => ft = C.TYPES[proj_uN_0 idx]! := by
  cases h
  dsimp only
  symm
  assumption

theorem function_type_of_typing {C : context} {ts : List types.FuncType} {idx entry ft}
    (h : Func_ok C (CodeEntry.function idx entry) ft)
    (hC : C.TYPES = ts.map EnvTranslation.funcType) : ft = functionType ts idx := by
  have hi := func_index_bound h
  have he := func_type_lookup h
  have hidx : idx.val < ts.length := by simpa [CodeEntry.function, hC, proj_uN_0] using hi
  rw [functionType_lookup hidx]
  change ft = C.TYPES[idx.val]! at he
  rw [hC, getElem!_pos _ _ (by simpa using hidx), List.getElem_map] at he
  exact he

theorem function_lists_of_typing {C : context} {ts : List types.FuncType} {indices codes fts}
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
