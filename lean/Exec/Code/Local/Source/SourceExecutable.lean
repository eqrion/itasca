import Exec.Code.Local.Source.SourceExecutableBody
import Exec.Code.Local.Source.SourceSlice
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Coverage of every independently decoded function body by the complete
execution source grammar. This predicate imposes no subset restriction. -/
def ModuleExecutable (raw : ModuleBinary.Module) : Prop :=
  ∀ entry ∈ raw.codes, Forall Abs.ExecutableInstr entry.body

namespace SourceExecutable
private theorem rep_all {α : Type} {R : α → List U8 → Prop} {P : α → Prop}
    (entry : ∀ value bytes, R value bytes → P value) {values bytes}
    (encoded : ModuleBinary.Rep R values bytes) : Forall P values := by
  induction encoded with
  | nil => simp [Forall]
  | cons first _ ih =>
    simpa [Forall, or_imp, forall_and] using And.intro (entry _ _ first) ih

private theorem padded_all {α : Type} {R : α → List U8 → Prop} {P : α → Prop}
    (entry : ∀ value bytes, R value bytes → P value) {id values bytes}
    (encoded : ModuleBinary.PaddedEncoding id (ModuleBinary.VecEncoding R) [] values bytes) :
    Forall P values := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp [Forall]
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, _, entriesEncoded, _⟩, _⟩ := content
    exact rep_all entry entriesEncoded

theorem body {profile data source} (encoded : Profile.BodyEncoding profile data source) :
    Forall Abs.ExecutableInstr source := by
  cases profile with
  | Wasm1 => exact body_wasm1 encoded
  | Wasm2 => exact body_wasm2 encoded

theorem body_bytes {profile source bytes} (encoded : Profile.BodyBytes profile source bytes) :
    Forall Abs.ExecutableInstr source := by
  cases profile with
  | Wasm1 =>
    obtain ⟨tokens, encoded, inner, rfl, emitted⟩ := encoded
    have known := rep_all (fun _ _ h => token_wasm1 h) encoded
    exact emits_wasm1 emitted (fun token member => known token (List.mem_append_left _ member))
  | Wasm2 =>
    obtain ⟨tokens, encoded, inner, rfl, emitted⟩ := encoded
    have known := rep_all (fun _ _ h => token_wasm2 h) encoded
    exact emits_wasm2 emitted (fun token member => known token (List.mem_append_left _ member))

theorem code {profile entry bytes} (encoded : Profile.CodeEncoding profile entry bytes) :
    Forall Abs.ExecutableInstr entry.body := by
  obtain ⟨size, locals, body, _, _, bodyEncoded, _⟩ := encoded
  exact body_bytes bodyEncoded

/-- Independent full-module encoding suffices for all executable source bodies;
no validator callback or compiler correctness assumption occurs. -/
theorem module {profile raw bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile) :
    ModuleExecutable raw := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, _, _, codeSection, _, _, _, _, _⟩ := encoded
  exact padded_all (fun _ _ h => code h) codeSection

/-- The canonical function-code list retains the coverage of its decoded bodies. -/
theorem functions {profile raw bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes profile) :
    ∀ source ∈ sourceFunctions raw, match source with
      | .HOST _ => False
      | .FUNC _ _ body => Forall Abs.ExecutableInstr body := by
  have all : ∀ (indices : List U32) (entries : List ModuleBinary.Code),
      (∀ entry ∈ entries, Forall Abs.ExecutableInstr entry.body) →
      ∀ source ∈ List.zipWith sourceFunctionCode indices entries, match source with
        | .HOST _ => False
        | .FUNC _ _ body => Forall Abs.ExecutableInstr body := by
    intro indices
    induction indices with
    | nil => simp
    | cons index indices ih =>
      intro entries known source member
      cases entries with
      | nil => simp at member
      | cons entry entries =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact known entry (by simp)
        · exact ih entries (fun e he => known e (by simp [he])) source member
  exact all raw.functions raw.codes (module encoded)

/-- The actual accepted validator result already carries the independent source
encoding needed for complete execution-language coverage. -/
theorem validated {profile bytes decoded}
    (validated : ModuleSound.Validated bytes decoded profile) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches decoded.env decoded.tail raw ∧ Module_ok (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Profile raw profile ∧ ModuleElaboration.AccessorTypes decoded.env raw ∧ ModuleExecutable raw := by
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := validated
  exact ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors, module encoded⟩
end SourceExecutable
end Exec.Code
