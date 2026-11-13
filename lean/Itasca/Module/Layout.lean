import Itasca.Module.Env.Declarations
import Itasca.Module.Sections.Tail
import Itasca.Module.Elab.TypingInversion
import Itasca.Profile.CodeEntry
import Itasca.Module.Code.Encoding
import Itasca.Module.Env.Encoding
import Itasca.Module.Code.LocalsComplete
import Itasca.Module.Env.Requirements
import Itasca.Module.Env.Complete
import Itasca.Module.Code.FuncTyping

/-!
Sections, each formerly its own module: Composition, Soundness, Limits, Layout.
-/

/-! ## Composition -/

section

/-!
# Composing the module regions

Joins the three independent byte regions (environment prefix, code section, tail) into one
`ModuleEncodingWith`. `encoding` works on byte lists and `whole_bytes` on adjacent spans of the
input slice, using the tail's end-of-input guarantee. Custom sections before the code section
are absorbed into the code section's padding.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleComposition

open ModuleBinary

/-- Custom sections can be prepended to a padded section. -/
theorem padded_prepend_custom {α : Type} {id : U8} {R : α → List U8 → Prop}
    {absent value before bytes} (hc : CustomsEncoding before)
    (hp : PaddedEncoding id R absent value bytes) :
    PaddedEncoding id R absent value (before ++ bytes) := by
  obtain ⟨customs, payload, hcustoms, hsection, he⟩ := hp
  exact ⟨before ++ customs, payload, ModuleTail.customs_append hc hcustoms,
    hsection, by simp [he, List.append_assoc]⟩

/-- The environment prefix, code section and tail encodings compose into one module encoding of
`before ++ codeBytes ++ tailBytes`. -/
theorem encoding {codeRel : Code → List U8 → Prop} {decls : ModuleEnv.Declarations} {codes segments before codeBytes tailBytes}
    (henv : ModuleEnv.PrefixEncoding decls before)
    (hcode : PaddedEncoding 10#u8 (VecEncoding codeRel) [] codes codeBytes)
    (htail : ModuleTail.Encoding segments tailBytes)
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

end Itasca.ModuleComposition

end

/-! ## Soundness -/

section

/-!
# Assembling `ModuleSound.Validated`

Defines `Validated`, the soundness certificate of an accepted module, and assembles it from the
decoded regions. `assembled` takes the environment, code and tail spans of one input slice, and
`assembled_regions` takes byte lists that tile the input. Both use the byte composition from
`Module/Composition` and the elaboration and typing results from `Module/Elab`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSound

open ModuleElaboration

/-- A raw module from the independent grammar that encodes exactly `data` under the
code encoding, elaborates to `moduleOf raw`, matches the returned environment and tail, satisfies
the generated `Module_ok`, meets the module restrictions, and has the types returned by the
public external-type accessors. -/
def Validated (data : Slice U8) (decoded : metadata.Module) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Itasca.Profile.CodeEncoding) raw data.val ∧
    Elaborates raw (moduleOf raw) ∧ Matches decoded.env decoded.tail raw ∧
    Module_ok (moduleOf raw) ∧ Restrictions raw ∧ AccessorTypes decoded.env raw

private theorem code_guards {env indices codes}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) indices codes) :
    env.data_count = none → ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    intro hc entry hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hp.no_data hc
    · exact ih hc entry hm

private theorem assembly_guards {env decls codes} {segments : List metadata.Data}
    (hr : ModuleEnv.Represents env decls)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (hc : ∀ count, env.data_count = some count → count.val = segments.length) :
    ModuleBinary.DataCountValid (decls.module codes (segments.map ModuleData.raw)) := by
  unfold ModuleBinary.DataCountValid
  change (match decls.dataCount with
    | none => ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false
    | some count => count.val = (segments.map ModuleData.raw).length)
  rw [hr.dataCount]
  cases he : env.data_count with
  | none => exact code_guards hcodes he
  | some count => simpa using hc count he

/-- Like `assembled`, from byte lists that tile `data` exactly as `before ++ codeBytes ++
tailBytes` instead of spans of one slice. Every semantic witness still belongs to one raw
module. -/
theorem assembled_regions {data : Slice U8} {env : metadata.Env} {tail : metadata.Tail}
    {decls : ModuleEnv.Declarations} {codes before codeBytes tailBytes}
    (hbytes : data.val = before ++ codeBytes ++ tailBytes)
    (henv : ModuleEnv.PrefixEncoding decls before)
    (hrep : ModuleEnv.Represents env decls) (hv : ModuleEnv.Valid env)
    (hcode : ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding (Itasca.Profile.CodeEncoding)) [] codes codeBytes)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (htail : ModuleTail.Encoding (tail.data.val.map ModuleData.raw) tailBytes)
    (hsegments : ∀ segment ∈ tail.data.val, ModuleData.Valid env segment)
    (hdataCount : ∀ count, env.data_count = some count → count.val = tail.data.val.length) :
    Validated data ⟨env, tail⟩ := by
  have hiNames : ∀ entry ∈ env.imports.val,
      wf_name (ModuleBinary.nameOfBytes entry.module.val) ∧ wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro e he
    exact henv.import_names_wf (ModuleEnv.rawImport e)
      (by rw [hrep.imports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  have heNames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro e he
    exact henv.export_names_wf (ModuleEnv.rawExport e)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨e, he, rfl⟩)
  obtain ⟨xts, hxts⟩ := hv.exports_resolve
  refine ⟨fromEnv env decls.tables decls.memories codes tail.data.val, ?_,
    elaborates hrep.cache hcodes, matches_fromEnv tail hrep.cache,
    typed hrep.cache hv hiNames heNames hcodes hsegments hdataCount hxts,
    restrictions hrep.cache hv hcodes, accessorTypes hrep.cache hv heNames⟩
  rw [hbytes, ← represents_module hrep]
  have hg := assembly_guards hrep hcodes hdataCount
  exact ModuleComposition.encoding henv hcode htail hg

end Itasca.ModuleSound

end

/-! ## Limits -/

section

/-!
# Resource bounds on module encodings

Strengthens the independent module grammar with the implementation caps that completeness needs:
`CodeEncodingWithinLimits` bounds one code entry, `ModuleEncodingWithinLimits` bounds the whole
encoding and every entry, and `ModuleSignaturesWithinLimits` bounds signature sizes. The caps
are `limits.MAX_*` constants and are separate from language validity. The file also lifts
relation weakening (`.imp`) through the grammar combinators.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem Rep.imp {α : Type} {R S : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (hs : ∀ value bs, R value bs → S value bs) : Rep S values bytes := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons (hs _ _ hp) ih

theorem VecEncoding.imp {α : Type} {R S : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) (hs : ∀ value bs, R value bs → S value bs) :
    VecEncoding S values bytes := by
  obtain ⟨count, entries, hn, he, hb⟩ := h
  exact ⟨count, entries, hn, he.imp hs, hb⟩

theorem PaddedEncoding.imp {α : Type} {R S : α → List U8 → Prop} {id absent value bytes}
    (h : PaddedEncoding id R absent value bytes) (hs : ∀ value bs, R value bs → S value bs) :
    PaddedEncoding id S absent value bytes := by
  obtain ⟨customs, sec, hc, hr, he⟩ := h
  refine ⟨customs, sec, hc, ?_, he⟩
  cases hr with
  | absent => exact .absent
  | present hp =>
    obtain ⟨size, payload, hn, hval, hb⟩ := hp
    exact .present ⟨size, payload, hn, hs _ _ hval, hb⟩

theorem ModuleEncodingWith.imp {R S : Code → List U8 → Prop} {raw bytes}
    (h : ModuleEncodingWith R raw bytes) (hs : ∀ code bs, R code bs → S code bs) :
    ModuleEncodingWith S raw bytes := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hcount, hc, hd, hcs, hb, hv⟩ := h
  exact ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, htt, hm, hg, he, hst, hel, hcount,
    hc.imp (fun _ _ hv => hv.imp hs), hd, hcs, hb, hv⟩

theorem ModuleEncodingWith.guards {R raw bytes}
    (h : ModuleEncodingWith R raw bytes) :
    DataCountValid raw := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := h
  exact hc

/-- A module encoding of at most `limits.MAX_MODULE_BYTES` bytes whose code entries satisfy
`CodeEncodingWithinLimits`. Only the code entries' encoding witnesses are strengthened. Padded
LEB encodings stay admitted, and the caps constrain the actual encoded body bytes. -/
def ModuleEncodingWithinLimits (raw : Module) (bytes : List U8) : Prop :=
  bytes.length ≤ limits.MAX_MODULE_BYTES.val ∧
    ModuleEncodingWith (Profile.CodeEncodingWithinLimits) raw bytes

/-- Forgetting the caps leaves a `ModuleEncodingWith` the plain code encoding. -/
theorem ModuleEncodingWithinLimits.encoding {raw bytes}
    (h : ModuleEncodingWithinLimits raw bytes) :
    ModuleEncodingWith (Profile.CodeEncoding) raw bytes :=
  h.2.imp (fun _ _ hc => hc.encoding)

/-- Every signature in the type section satisfies `Profile.FuncTypeWithinLimits`. This is an
implementation cap on parameters and results, required for
completeness only. -/
def ModuleSignaturesWithinLimits (raw : Module) : Prop :=
  ∀ ft ∈ raw.types, Profile.FuncTypeWithinLimits ft

end Itasca.ModuleBinary

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

namespace Itasca.ModuleLayout

open ModuleBinary

/-- The code section occupies `start` to `finish` with entries `entries`, or it is absent and
`ModuleCode.AbsentAt` holds at `start`. The absence case carries the lookahead that the parser
performs, which an empty optional byte span alone does not justify. -/
def CodeAt (data : Slice U8) (start : Usize) (entries : List Code) (finish : Usize) : Prop :=
  At (SectionEncoding 10#u8 (VecEncoding (Profile.CodeEncodingWithinLimits))) data start entries finish ∨
    entries = [] ∧ finish = start ∧ ModuleCode.AbsentAt data start

/-- Independent byte spans for the environment prefix, code section and tail, arranged as the
greedy environment, code and tail parsers consume them. `stop` says that `codePos` is a place
where the environment scan stops (EOF, or a code or data section header). -/
structure Layout (data : Slice U8) (raw : Module) (decls : ModuleEnv.Declarations)
    (codePos tailPos : Usize) : Prop where
  raw_eq : raw = decls.module raw.codes raw.data
  environment : At (fun ds bs => ModuleEnv.PrefixEncoding ds bs) data 0#usize decls codePos
  code : CodeAt data codePos raw.codes tailPos
  tail : At (fun ds bs => ModuleTail.Encoding ds bs) data tailPos raw.data (Slice.len data)
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
theorem normalize (data : Slice U8) (raw : Module)
    (h : ModuleEncodingWithinLimits raw data.val) :
    ∃ decls codePos tailPos, Layout data raw decls codePos tailPos := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, ht, hi, hf, hta, hm, hg, he, hst, hel, hcount, hc, hd, hcustom, hbytes, hcountValid⟩ := h.2
  let decls : ModuleEnv.Declarations :=
    ⟨raw.types, raw.imports, raw.functions, raw.tables, raw.memories, raw.globals,
      raw.exports, raw.start, raw.elements, raw.dataCount⟩
  have hr : raw = decls.module raw.codes raw.data := by cases raw; rfl
  let before := magicVersion ++ types ++ imports ++ functions ++ tables ++ memories ++
    globals ++ exports ++ start ++ elements ++ dataCount
  have hp : ∀ cs, CustomsEncoding cs → ModuleEnv.PrefixEncoding decls (before ++ cs) := by
    intro cs hs
    refine ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
      cs, ht, hi, hf, hta, hm, hg, he, hst, hel, hcount, hs, rfl⟩
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
        (show At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor))) data codePos raw.data dataEnd from
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
      (show At (SectionEncoding 10#u8 (VecEncoding (Profile.CodeEncodingWithinLimits)))
        data codePos raw.codes tailPos from ⟨codeBytes, hcode, hc⟩).section_split
    exact ⟨decls, codePos, tailPos, hr, ⟨_, hprefix, hb⟩,
      .inl ⟨codeBytes, hcode, hc⟩, ⟨_, ⟨datas, customs, hd, hcustom, rfl⟩, ht⟩,
      .inr ⟨10#u8, first, tailPos, hheader, by decide⟩⟩

end Itasca.ModuleLayout

open Aeneas Aeneas.Std

namespace Itasca.ModuleLayout

open ModuleBinary ModuleElaboration

/-- Generated function typing and the independent declaration condition give `CodeEntry.Typed`
for every code entry against the decoded environment. No premise about entry validation is
used. -/
theorem CodeAt.typed {raw decls env}
    (hr : ModuleEnv.Ready raw 10 decls env)
    (ht : SectionsTyped raw) (hdata : DataCountValid raw)
    (hdeclared : ∀ entry ∈ raw.codes, DeclaredReferences.Instructions
      (env.declared_funcs.val.map (fun idx => uN.mk_uN idx.val)) entry.body) :
    List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val raw.codes := by
  rw [hr.functions_eq (by omega)]
  refine List.forall₂_iff_zip.mpr ⟨ht.functions.length_eq, ?_⟩
  intro idx entry hm
  have hfunc := (List.forall₂_iff_zip.mp ht.functions).2 hm
  have hentry : entry ∈ raw.codes := (List.of_mem_zip hm).2
  apply CodeEntry.Typed.of_func_ok (hr.moduleContext (by omega))
    (hr.elements_context (by omega)) (hr.data_context (by omega) hdata entry hentry) hfunc
    (hdeclared entry hentry)

end Itasca.ModuleLayout

end
