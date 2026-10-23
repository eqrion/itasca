import Itasca.Module.Limits
import Itasca.Module.Env.NameFacts
import Itasca.Module.Code.Section
import Itasca.Module.Composition
import Itasca.Module.Env.Requirements
import Itasca.Module.Env.ReadyContexts
import Itasca.Module.Code.FuncTyping

/-!
# Byte layout of a limited module encoding

Splits an independent `ModuleEncodingWithinLimits` encoding into the regions that the greedy
environment, code and tail parsers consume. `Layout` records the spans, `normalize` produces a
`Layout` for every limited encoding, and `CodeAt.typed` transports generated function typing to
`CodeEntry.Typed` for the decoded environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleLayout

open ModuleBinary

/-- The code section occupies `start` to `finish` with entries `entries`, or it is absent and
`ModuleCode.AbsentAt` holds at `start`. The absence case carries the lookahead that the parser
performs, which an empty optional byte span alone does not justify. -/
def CodeAt (data : Slice U8) (start : Usize) (entries : List Code) (finish : Usize) (profile : ValidationProfile := .Wasm1) : Prop :=
  At (SectionEncoding 10#u8 (VecEncoding (Profile.CodeEncodingWithinLimits profile))) data start entries finish ∨
    entries = [] ∧ finish = start ∧ ModuleCode.AbsentAt data start

/-- Independent byte spans for the environment prefix, code section and tail, arranged as the
greedy environment, code and tail parsers consume them. `stop` says that `codePos` is a place
where the environment scan stops (EOF, or a code or data section header). -/
structure Layout (data : Slice U8) (raw : Module) (decls : ModuleEnv.Declarations)
    (codePos tailPos : Usize) (profile : ValidationProfile := .Wasm1) : Prop where
  raw_eq : raw = decls.module raw.codes raw.data
  environment : At (fun ds bs => ModuleEnv.PrefixEncoding ds bs profile) data 0#usize decls codePos
  code : CodeAt data codePos raw.codes tailPos profile
  tail : At (fun ds bs => ModuleTail.Encoding ds bs profile) data tailPos raw.data (Slice.len data)
  stop : ModuleEnv.StopAt data codePos

private theorem whole (data : Slice U8) : Wasm1.BytesAt data 0#usize data.val (Slice.len data) := by
  constructor <;> simp

private theorem split_three {data : Slice U8} {before code tail : List U8}
    (h : data.val = before ++ code ++ tail) :
    ∃ codePos tailPos, Wasm1.BytesAt data 0#usize before codePos ∧
      Wasm1.BytesAt data codePos code tailPos ∧
      Wasm1.BytesAt data tailPos tail (Slice.len data) := by
  have hs : Wasm1.BytesAt data 0#usize (before ++ (code ++ tail)) (Slice.len data) := by
    simpa [h, List.append_assoc] using whole data
  obtain ⟨codePos, hb, hr⟩ := hs.split
  obtain ⟨tailPos, hc, ht⟩ := hr.split
  exact ⟨codePos, tailPos, hb, hc, ht⟩

private theorem optional_cases {α : Type} {id R absent value bytes}
    (h : @OptionalSectionEncoding α id R absent value bytes) :
    (value = absent ∧ bytes = []) ∨ SectionEncoding id R value bytes := by
  cases h with
  | absent => exact .inl ⟨rfl, rfl⟩
  | present hs => exact .inr hs

/-- Every limited module encoding has a `Layout`. Custom sections before an absent code section
belong to the environment scan, which stops at the next data section header or at EOF. -/
theorem normalize {profile} (data : Slice U8) (raw : Module)
    (h : ModuleEncodingWithinLimits raw data.val profile) :
    ∃ decls codePos tailPos, Layout data raw decls codePos tailPos profile := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, hta, hm, hg, he, hst, hel, hcount, hc, hd, hcustom, hbytes, hallowed, hcountValid⟩ := h.2
  let decls : ModuleEnv.Declarations :=
    ⟨raw.types, raw.imports, raw.functions, raw.tables, raw.memories, raw.globals,
      raw.exports, raw.start, raw.elements, raw.dataCount⟩
  have hr : raw = decls.module raw.codes raw.data := by cases raw; rfl
  let before := magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
    globals ++ exports ++ start ++ elements ++ dataCount
  have hp : ∀ cs, CustomsEncoding cs → ModuleEnv.PrefixEncoding decls (before ++ cs) profile := by
    intro cs hs
    refine ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
      cs, ht, hi, hf, hta, hm, hg, he, hst, hel, hcount, hs, rfl, ?_⟩
    exact ⟨hallowed.1, hallowed.2.1, hallowed.2.2.1, hallowed.2.2.2.1,
      by simp [decls, ModuleEnv.Declarations.module], hallowed.2.2.2.2.2.1,
      by simp [decls, ModuleEnv.Declarations.module]⟩
  obtain ⟨codeCustoms, codeBytes, hcc, hcode, hcodes⟩ := hc
  rcases optional_cases hcode with ⟨hnoCode, hcempty⟩ | hcode
  · obtain ⟨dataCustoms, dataBytes, hdc, hdata, hdatas⟩ := hd
    rcases optional_cases hdata with ⟨hnoData, hdempty⟩ | hdata
    · have hprefix := hp (codeCustoms ++ dataCustoms ++ customs)
        (ModuleTail.customs_append (ModuleTail.customs_append hcc hdc) hcustom)
      have hb : data.val = before ++ (codeCustoms ++ dataCustoms ++ customs) := by
        simpa [before, hcodes, hdatas, hcempty, hdempty, List.append_assoc] using hbytes
      refine ⟨decls, Slice.len data, Slice.len data, hr, ?_, ?_, ?_, .inl rfl⟩
      · exact ⟨_, hprefix, by simpa [hb] using whole data⟩
      · exact .inr ⟨hnoCode, rfl, .inl (by simp)⟩
      · refine ⟨[], ?_, Wasm1.BytesAt.nil data (Slice.len data) (by simp)⟩
        rw [hnoData]
        exact ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩
    · have hprefix := hp (codeCustoms ++ dataCustoms) (ModuleTail.customs_append hcc hdc)
      have hb : data.val = (before ++ (codeCustoms ++ dataCustoms)) ++ [] ++
          (dataBytes ++ customs) := by
        simpa [before, hcodes, hdatas, hcempty, List.append_assoc] using hbytes
      obtain ⟨codePos, tailPos, hb, hc, ht⟩ := split_three hb
      have hsame := hc.empty
      subst tailPos
      obtain ⟨dataEnd, hdataSpan, _⟩ := ht.split
      obtain ⟨first, hheader, _⟩ :=
        (show At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor profile))) data codePos raw.data dataEnd from
          ⟨dataBytes, hdata, hdataSpan⟩).section_split
      exact ⟨decls, codePos, codePos, hr, ⟨_, hprefix, hb⟩,
        .inr ⟨hnoCode, rfl, .inr ⟨11#u8, first, dataEnd, hheader, by decide⟩⟩,
        ⟨_, ⟨dataBytes, customs, ⟨[], dataBytes, .nil, .present hdata, by simp⟩,
          hcustom, rfl⟩, ht⟩,
        .inr ⟨11#u8, first, dataEnd, hheader, by decide⟩⟩
  · have hprefix := hp codeCustoms hcc
    have hb : data.val = (before ++ codeCustoms) ++ codeBytes ++ (datas ++ customs) := by
      simpa [before, hcodes, List.append_assoc] using hbytes
    obtain ⟨codePos, tailPos, hb, hc, ht⟩ := split_three hb
    obtain ⟨first, hheader, _⟩ :=
      (show At (SectionEncoding 10#u8 (VecEncoding (Profile.CodeEncodingWithinLimits profile)))
        data codePos raw.codes tailPos from ⟨codeBytes, hcode, hc⟩).section_split
    exact ⟨decls, codePos, tailPos, hr, ⟨_, hprefix, hb⟩,
      .inl ⟨codeBytes, hcode, hc⟩, ⟨_, ⟨datas, customs, hd, hcustom, rfl⟩, ht⟩,
      .inr ⟨10#u8, first, tailPos, hheader, by decide⟩⟩

end Itasca.ModuleLayout

open Aeneas Aeneas.Std

namespace Itasca.ModuleLayout

open ModuleBinary ModuleElaboration

/-- Generated function typing and the independent profile restrictions give `CodeEntry.Typed`
for every code entry against the decoded environment. No premise about entry validation is
used. -/
theorem CodeAt.typed {profile raw decls env}
    (hr : ModuleEnv.Ready raw 10 decls env)
    (ht : SectionsTyped raw) (hp : Profile raw profile)
    (hallowed : ModuleTypesAllowed profile raw) (hdata : DataCountValid raw)
    (hdeclared : ∀ entry ∈ raw.codes, DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val raw.codes := by
  rw [hr.functions_eq (by omega)]
  refine List.forall₂_iff_zip.mpr ⟨ht.functions.length_eq, ?_⟩
  intro idx entry hm
  have hfunc := (List.forall₂_iff_zip.mp ht.functions).2 hm
  have hprofile := (List.forall₂_iff_zip.mp hp.bodies).2 hm
  have hentry : entry ∈ raw.codes := (List.of_mem_zip hm).2
  apply CodeEntry.Typed.of_func_ok (hr.moduleContext (by omega))
    (hr.elements_context (by omega)) (hr.data_context (by omega) hdata entry hentry) _ hfunc
    (hallowed.2.2.2.2.1 entry hentry) (hdeclared entry hentry)
  simpa [hr.types_eq (by omega)] using hprofile

end Itasca.ModuleLayout
