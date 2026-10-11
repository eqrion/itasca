import Itasca.Module.ModuleDeclarations
import Itasca.Binary.ModuleUnicodeUnique

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- Every vector member retains its own independent byte-format witness. -/
theorem Rep.member {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) {value} (hm : value ∈ values) : ∃ bs, R value bs := by
  induction h with
  | nil => simp at hm
  | cons hv _ ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, hv⟩
      · exact ih hm

theorem VecEncoding.member {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) {value} (hm : value ∈ values) : ∃ bs, R value bs := by
  obtain ⟨_, _, _, hr, _⟩ := h
  exact hr.member hm

theorem PaddedEncoding.member {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    {value} (hm : value ∈ values) : ∃ bs, R value bs := by
  obtain ⟨_, _, _, hs, _⟩ := h
  cases hs with
  | absent => simp at hm
  | present hp =>
      obtain ⟨_, _, _, hr, _⟩ := hp
      exact hr.member hm

theorem ImportEncoding.names_wf {entry bytes} (h : ImportEncoding entry bytes) :
    wf_name (nameOfBytes entry.moduleName) ∧ wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, hmodule, hname, _, _⟩ := h
  exact ⟨hmodule.wellFormed, hname.wellFormed⟩

theorem ExportEncoding.name_wf {entry bytes} (h : ExportEncoding entry bytes) :
    wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, hname, _, _⟩ := h
  exact hname.wellFormed

end Itasca.ModuleBinary

namespace Itasca.ModuleEnv

open ModuleBinary

/-- The prefix grammar supplies the Unicode-name size bounds as well as scalar
validity, without adding assumptions about nested runtime vector lengths. -/
theorem PrefixEncoding.import_names_wf {decls bytes} (h : PrefixEncoding decls bytes) :
    ∀ entry ∈ decls.imports,
      wf_name (nameOfBytes entry.moduleName) ∧ wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hi, _⟩ := h
  intro entry hm
  obtain ⟨bs, he⟩ := hi.member hm
  exact he.names_wf

theorem PrefixEncoding.export_names_wf {decls bytes} (h : PrefixEncoding decls bytes) :
    ∀ entry ∈ decls.exports, wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _⟩ := h
  intro entry hm
  obtain ⟨bs, hx⟩ := he.member hm
  exact hx.name_wf

end Itasca.ModuleEnv
