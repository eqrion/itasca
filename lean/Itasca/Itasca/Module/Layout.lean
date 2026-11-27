import Itasca.Module.Definitions
import Itasca.Binary.ReadModule
import Itasca.Module.Env.Declarations
import Itasca.Module.Sections.EnvironmentAndTail
import Itasca.Module.Elab.ToTyping
import Itasca.CodeEntry.Encoding
import Itasca.Module.Code.ContextTransport
import Itasca.Module.Env.Encoding
import Itasca.Module.Code.Framing
import Itasca.Module.Env.Requirements
import Itasca.Module.Env.Complete
import Itasca.Module.Code.FuncTyping

open WebAssembly

/-! ## Composition -/

section

/-!
# Composing the module regions

`Module.Composition.encoding` joins independent environment, code and tail byte
lists into `ModuleEncodingWith`. `Module.Sound.assembled_regions` assembles
adjacent input spans and their typing witnesses into `Validated`, including the
data-count guard. Custom sections preceding code belong to its padding.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Composition

open Itasca.Binary

/-- Custom sections can be prepended to a padded section. -/
theorem padded_prepend_custom {α : Type} {id : U8} {R : α → List U8 → Prop}
    {absent value before bytes} (hc : CustomsEncoding before)
    (hp : PaddedEncoding id R absent value bytes) :
    PaddedEncoding id R absent value (before ++ bytes) := by
  obtain ⟨customs, payload, hcustoms, hsection, he⟩ := hp
  exact ⟨before ++ customs, payload, Module.Tail.customs_append hc hcustoms,
    hsection, by simp [he, List.append_assoc]⟩

/-- The environment prefix, code section and tail encodings compose into one module encoding of
`before ++ codeBytes ++ tailBytes`. -/
theorem encoding {codeRel : Code → List U8 → Prop} {decls : Module.Environment.Declarations} {codes segments before codeBytes tailBytes}
    (henv : Module.Environment.PrefixEncoding decls before)
    (hcode : PaddedEncoding 10#u8 (VecEncoding codeRel) [] codes codeBytes)
    (htail : Module.Tail.Encoding segments tailBytes)
    (hcount : DataCountValid (decls.module codes segments)) :
    ModuleEncodingWith codeRel (decls.module codes segments) (before ++ codeBytes ++ tailBytes) := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start,
    elements, dataCount, customs, htypes, himports, hfunctions, htables, hmemories, hglobals,
    hexports, hstart, helements, hdataCount, hcustoms, he⟩ := henv
  obtain ⟨datas, trailing, hdatas, htrailing, ht⟩ := htail
  refine ⟨types, imports, functions, tables, memories, globals, exports, start,
    elements, dataCount, customs ++ codeBytes, datas, trailing, htypes, himports, hfunctions,
    htables, hmemories, hglobals, hexports, hstart, helements, hdataCount,
    padded_prepend_custom hcustoms hcode, hdatas, htrailing, ?_, hcount⟩
  simp only [he, ht, List.append_assoc]
  rfl

end Itasca.Module.Composition

end

/-! ## Soundness -/

section

/-!
# Assembling `Module.Sound.Validated`

Assembles the public `Validated` certificate from decoded regions. `assembled` takes
environment, code and tail spans of one input slice; `assembled_regions` takes byte lists
tiling the input. Their composition uses the layout lemmas here and the elaboration and
typing results under `Module/Elab`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sound

open Module.Elaboration

private theorem code_guards {env indices codes}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) indices codes) :
    env.data_count = none → ∀ entry ∈ codes, Binary.instructionsUseData entry.body = false := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    intro hc entry hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hp.no_data hc
    · exact ih hc entry hm

private theorem assembly_guards {env decls codes} {segments : List metadata.Data}
    (hr : Module.Environment.Represents env decls)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (hc : ∀ count, env.data_count = some count → count.val = segments.length) :
    Binary.DataCountValid (decls.module codes (segments.map Module.Data.raw)) := by
  simp only [Binary.DataCountValid, WebAssembly.Binary.DataCountValidWith, Module.Environment.Declarations.module]
  rw [hr.dataCount]
  cases he : env.data_count with
  | none => exact code_guards hcodes he
  | some count => simpa using hc count he

/-- Like `assembled`, from byte lists that tile `data` exactly as `before ++ codeBytes ++
tailBytes` instead of spans of one slice. Every semantic witness still belongs to one raw
module. -/
theorem assembled_regions {data : Slice U8} {env : metadata.Env} {tail : metadata.Tail}
    {decls : Module.Environment.Declarations} {codes before codeBytes tailBytes}
    (hbytes : data.val = before ++ codeBytes ++ tailBytes)
    (henv : Module.Environment.PrefixEncoding decls before)
    (hrep : Module.Environment.Represents env decls) (hv : Module.Environment.Valid env)
    (hcode : Binary.PaddedEncoding 10#u8
      (Binary.VecEncoding (Itasca.CodeEntry.CodeEncoding)) [] codes codeBytes)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (htail : Module.Tail.Encoding (tail.data.val.map Module.Data.raw) tailBytes)
    (hsegments : ∀ segment ∈ tail.data.val, Module.Data.Valid env segment)
    (hdataCount : ∀ count, env.data_count = some count → count.val = tail.data.val.length) :
    Validated data ⟨env, tail⟩ := by
  have hiNames : ∀ entry ∈ env.imports.val,
      wf_name (Binary.nameOfBytes entry.module.val) ∧ wf_name (Binary.nameOfBytes entry.name.val) := by
    intro e he
    exact henv.import_names_wf (Module.Environment.rawImport e)
      (by rw [hrep.imports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  have heNames : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val) := by
    intro e he
    exact henv.export_names_wf (Module.Environment.rawExport e)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  obtain ⟨xts, hxts⟩ := hv.exports_resolve
  refine ⟨fromEnv env decls.tables decls.memories codes tail.data.val, ?_,
    elaborates hrep.cache hcodes, matches_from_env tail hrep.cache,
    typed hrep.cache hv hiNames heNames hcodes hsegments hdataCount hxts,
    restrictions hrep.cache hv hcodes, accessor_types hrep.cache hv heNames⟩
  rw [hbytes, ← represents_module hrep]
  have hg := assembly_guards hrep hcodes hdataCount
  exact Binary.Source.moduleEncoding (Module.Composition.encoding henv hcode htail hg)

end Itasca.Module.Sound

end

/-! ## Layout -/

section

/-!
# Byte layout of a limited module encoding

Splits an independent `ModuleEncodingWithinLimits` encoding into the regions that the greedy
environment, code and tail parsers consume. `Layout` records the spans, `normalize` produces a
`Layout` for every limited encoding, and `CodeAt.typed` transports generated function typing to
`CodeEntry.Typed` for the decoded environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module

open Itasca.Binary

/-- The code section occupies `start` to `finish` with entries `entries`, or it is absent and
`Module.Code.AbsentAt` holds at `start`. The absence case carries the lookahead that the parser
performs, which an empty optional byte span alone does not justify. -/
def CodeAt (data : Slice U8) (start : Usize) (entries : List Code) (finish : Usize) : Prop :=
  At (SectionEncoding 10#u8 (VecEncoding (CodeEntry.CodeEncodingWithinLimits))) data start entries finish ∨
    entries = [] ∧ finish = start ∧ Module.Code.AbsentAt data start

/-- Independent byte spans for the environment prefix, code section and tail, arranged as the
greedy environment, code and tail parsers consume them. `stop` says that `codePos` is a place
where the environment scan stops (EOF, or a code or data section header). -/
structure Layout (data : Slice U8) (raw : Module) (decls : Module.Environment.Declarations)
    (codePos tailPos : Usize) : Prop where
  raw_eq : raw = decls.module raw.codes raw.data
  environment : At (fun ds bs => Module.Environment.PrefixEncoding ds bs) data 0#usize decls codePos
  code : CodeAt data codePos raw.codes tailPos
  tail : At (fun ds bs => Module.Tail.Encoding ds bs) data tailPos raw.data (Slice.len data)
  stop : Module.Environment.StopAt data codePos

private theorem whole (data : Slice U8) : Body.Scalar.BytesAt data 0#usize data.val (Slice.len data) := by
  constructor <;> simp

private theorem split_three {data : Slice U8} {before code tail : List U8}
    (h : data.val = before ++ code ++ tail) :
    ∃ codePos tailPos, Body.Scalar.BytesAt data 0#usize before codePos ∧
      Body.Scalar.BytesAt data codePos code tailPos ∧
      Body.Scalar.BytesAt data tailPos tail (Slice.len data) := by
  have hs : Body.Scalar.BytesAt data 0#usize (before ++ (code ++ tail)) (Slice.len data) := by
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
theorem normalize (data : Slice U8) (raw : Module)
    (h : ModuleEncodingWithinLimits raw data.val) :
    ∃ decls codePos tailPos, Layout data raw decls codePos tailPos := by
  have spans := Source.limitedReaderSpans h.2
  rw [Source.readerBytes_bytes] at spans
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, hta, hm, hg, he, hst, hel, hcount, hc, hd, hcustom, hbytes, hcountValid⟩ := spans
  change data.val = magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++ globals ++
    exports ++ start ++ elements ++ dataCount ++ codes ++ datas ++ customs at hbytes
  let decls : Module.Environment.Declarations :=
    ⟨raw.types, raw.imports, raw.functions, raw.tables, raw.memories, raw.globals,
      raw.exports, raw.start, raw.elements, raw.dataCount⟩
  have hr : raw = decls.module raw.codes raw.data := by cases raw; rfl
  let before := magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
    globals ++ exports ++ start ++ elements ++ dataCount
  have hp : ∀ cs, CustomsEncoding cs → Module.Environment.PrefixEncoding decls (before ++ cs) := by
    intro cs hs
    refine ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
      cs, ht, hi, hf, hta, hm, hg, he, hst, hel, hcount, hs, rfl⟩
  obtain ⟨codeCustoms, codeBytes, hcc, hcode, hcodes⟩ := hc
  rcases optional_cases hcode with ⟨hnoCode, hcempty⟩ | hcode
  · obtain ⟨dataCustoms, dataBytes, hdc, hdata, hdatas⟩ := hd
    rcases optional_cases hdata with ⟨hnoData, hdempty⟩ | hdata
    · have hprefix := hp (codeCustoms ++ dataCustoms ++ customs)
        (Module.Tail.customs_append (Module.Tail.customs_append hcc hdc) hcustom)
      have hb : data.val = before ++ (codeCustoms ++ dataCustoms ++ customs) := by
        simpa [before, hcodes, hdatas, hcempty, hdempty, List.append_assoc] using hbytes
      refine ⟨decls, Slice.len data, Slice.len data, hr, ?_, ?_, ?_, .inl rfl⟩
      · exact ⟨_, hprefix, by simpa [hb] using whole data⟩
      · exact .inr ⟨hnoCode, rfl, .inl (by simp)⟩
      · refine ⟨[], ?_, Body.Scalar.BytesAt.nil data (Slice.len data) (by simp)⟩
        change raw.data = [] at hnoData
        rw [hnoData]
        exact ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩
    · have hprefix := hp (codeCustoms ++ dataCustoms) (Module.Tail.customs_append hcc hdc)
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
      (show At (SectionEncoding 10#u8 (VecEncoding (CodeEntry.CodeEncodingWithinLimits)))
        data codePos raw.codes tailPos from ⟨codeBytes, hcode, hc⟩).section_split
    exact ⟨decls, codePos, tailPos, hr, ⟨_, hprefix, hb⟩,
      .inl ⟨codeBytes, hcode, hc⟩, ⟨_, ⟨datas, customs, hd, hcustom, rfl⟩, ht⟩,
      .inr ⟨10#u8, first, tailPos, hheader, by decide⟩⟩

end Itasca.Module

open Aeneas Aeneas.Std

namespace Itasca.Module

open Itasca.Binary Module.Elaboration

/-- Generated function typing and the independent declaration condition give `CodeEntry.Typed`
for every code entry against the decoded environment. No premise about entry validation is
used. -/
theorem CodeAt.typed {raw decls env}
    (hr : Module.Environment.Ready raw 10 decls env)
    (ht : SectionsTyped raw) (hdata : DataCountValid raw)
    (hdeclared : ∀ entry ∈ raw.codes, Spec.DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val raw.codes := by
  rw [hr.functions_eq (by omega)]
  refine List.forall₂_iff_zip.mpr ⟨ht.functions.length_eq, ?_⟩
  intro idx entry hm
  have hfunc := (List.forall₂_iff_zip.mp ht.functions).2 hm
  have hentry : entry ∈ raw.codes := (List.of_mem_zip hm).2
  apply CodeEntry.Typed.of_func_ok (hr.module_context (by omega))
    (hr.elements_context (by omega)) (hr.data_context (by omega) hdata entry hentry) hfunc
    (hdeclared entry hentry)

end Itasca.Module

end
