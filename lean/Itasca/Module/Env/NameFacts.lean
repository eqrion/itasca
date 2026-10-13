import Itasca.Module.Env.Declarations
import Itasca.Binary.UnicodeUnique

/-!
# Name facts from the prefix grammar

Consequences of `PrefixEncoding` for import and export names: every member of an encoded vector has
its own byte encoding (`VecEncoding.member`), and import and export names are well-formed Unicode
names (`PrefixEncoding.import_names_wf`, `PrefixEncoding.export_names_wf`).
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- Every member of a related list has its own byte-format witness. -/
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

/-- Import module and field names in an encoded prefix are well-formed Unicode names. -/
theorem PrefixEncoding.import_names_wf {decls bytes profile} (h : PrefixEncoding decls bytes profile) :
    ∀ entry ∈ decls.imports,
      wf_name (nameOfBytes entry.moduleName) ∧ wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hi, _⟩ := h
  intro entry hm
  obtain ⟨bs, he⟩ := hi.member hm
  exact he.names_wf

/-- Export names in an encoded prefix are well-formed Unicode names. -/
theorem PrefixEncoding.export_names_wf {decls bytes profile} (h : PrefixEncoding decls bytes profile) :
    ∀ entry ∈ decls.exports, wf_name (nameOfBytes entry.name) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he, _⟩ := h
  intro entry hm
  obtain ⟨bs, hx⟩ := he.member hm
  exact hx.name_wf

end Itasca.ModuleEnv
