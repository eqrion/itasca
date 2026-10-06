import Itasca.ModuleLimits
import Itasca.ModuleCodeComplete
import Itasca.ModuleComposition
import Itasca.ModuleEnvRequirements

open Aeneas Aeneas.Std

namespace Itasca.ModuleLayout

open ModuleBinary

/-- The code boundary retains the absence lookahead required by the actual
parser; an empty optional byte span alone does not justify that lookahead. -/
def CodeAt (data : Slice U8) (start : Usize) (entries : List Code) (finish : Usize) : Prop :=
  At (SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits)) data start entries finish ∨
    entries = [] ∧ finish = start ∧ ModuleCode.AbsentAt data start

theorem CodeAt.optional {data start entries finish} (h : CodeAt data start entries finish) :
    At (OptionalSectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits) [])
      data start entries finish := by
  rcases h with ⟨bytes, he, hs⟩ | ⟨he, hn, hstop⟩
  · exact ⟨bytes, .present he, hs⟩
  · subst entries
    subst finish
    have hb : start.val ≤ data.length := by
      rcases hstop with h | ⟨_, _, _, hh, _⟩
      · omega
      · have := hh.span; omega
    exact ⟨[], .absent, Wasm.BytesAt.nil data start hb⟩

theorem CodeAt.segmentFree {data start entries finish} (h : CodeAt data start entries finish)
    {entry : Code} (hm : entry ∈ entries) : Forall BodyContext.SegmentFree entry.body := by
  rcases h with ⟨bytes, hs, _⟩ | ⟨he, _, _⟩
  · obtain ⟨_, _, _, hv, _⟩ := hs
    obtain ⟨_, _, _, _, _, _, _, hbody, _, _⟩ := hv.member hm
    exact BodyContext.body_segmentFree hbody
  · simp [he] at hm

theorem CodeAt.complete {data start entries finish} (h : CodeAt data start entries finish)
    (env : module.Env) (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (htyped : List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val entries) :
    module.validate_code data start env = .ok (.Ok finish) := by
  rcases h with hs | ⟨he, hn, hstop⟩
  · exact module.validate_code.complete_present data env start finish entries hsize henv hbound htyped hs
  · subst entries
    subst finish
    have hnil : env.func_type_indices.val = [] := by simpa using htyped
    exact module.validate_code.complete_absent data env start hsize hnil hstop

/-- Independent byte spans arranged exactly as the greedy environment/code/tail
parser consumes them. The raw module and all per-body limits are unchanged. -/
structure Layout (data : Slice U8) (raw : Module) (decls : ModuleEnv.Declarations)
    (codePos tailPos : Usize) : Prop where
  raw_eq : raw = decls.module raw.codes raw.data
  environment : At ModuleEnv.PrefixEncoding data 0#usize decls codePos
  code : CodeAt data codePos raw.codes tailPos
  tail : At ModuleTail.Encoding data tailPos raw.data (Slice.len data)
  stop : ModuleEnv.StopAt data codePos

private theorem whole (data : Slice U8) : Wasm.BytesAt data 0#usize data.val (Slice.len data) := by
  constructor <;> simp

private theorem split_three {data : Slice U8} {before code tail : List U8}
    (h : data.val = before ++ code ++ tail) :
    ∃ codePos tailPos, Wasm.BytesAt data 0#usize before codePos ∧
      Wasm.BytesAt data codePos code tailPos ∧
      Wasm.BytesAt data tailPos tail (Slice.len data) := by
  have hs : Wasm.BytesAt data 0#usize (before ++ (code ++ tail)) (Slice.len data) := by
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

/-- Custom sections preceding an absent code section are consumed by the
preceding environment scan, through the next data header or EOF. -/
theorem normalize (data : Slice U8) (raw : Module)
    (h : ModuleEncodingWithinLimits raw data.val) :
    ∃ decls codePos tailPos, Layout data raw decls codePos tailPos := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements,
    codes, datas, customs, ht, hi, hf, hta, hm, hg, he, hst, hel, hc, hd, hcustom, hbytes⟩ := h.2
  let decls : ModuleEnv.Declarations :=
    ⟨raw.types, raw.imports, raw.functions, raw.tables, raw.memories, raw.globals,
      raw.exports, raw.start, raw.elements⟩
  have hr : raw = decls.module raw.codes raw.data := by cases raw; rfl
  let before := magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
    globals ++ exports ++ start ++ elements
  have hp : ∀ cs, CustomsEncoding cs → ModuleEnv.PrefixEncoding decls (before ++ cs) := by
    intro cs hs
    exact ⟨types, imports, functions, tables, memories, globals, exports, start, elements,
      cs, ht, hi, hf, hta, hm, hg, he, hst, hel, hs, rfl⟩
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
      · refine ⟨[], ?_, Wasm.BytesAt.nil data (Slice.len data) (by simp)⟩
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
        (show At (SectionEncoding 11#u8 (VecEncoding DataEncoding)) data codePos raw.data dataEnd from
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
      (show At (SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits))
        data codePos raw.codes tailPos from ⟨codeBytes, hcode, hc⟩).section_split
    exact ⟨decls, codePos, tailPos, hr, ⟨_, hprefix, hb⟩,
      .inl ⟨codeBytes, hcode, hc⟩, ⟨_, ⟨datas, customs, hd, hcustom, rfl⟩, ht⟩,
      .inr ⟨10#u8, first, tailPos, hheader, by decide⟩⟩

end Itasca.ModuleLayout
