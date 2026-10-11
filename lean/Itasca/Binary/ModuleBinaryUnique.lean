import Itasca.Binary.ModuleBinaryUniqueSections

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

namespace SectionDecode

/-- Standard fields recovered from the unique raw section framing. -/
structure Fields (raw : Module) (sections : List (U8 × List U8)) : Prop where
  types : Field (VecEncoding FuncTypeEncoding) [] raw.types (payloads 1#u8 sections)
  imports : Field (VecEncoding ImportEncoding) [] raw.imports (payloads 2#u8 sections)
  functions : Field (VecEncoding IndexEncoding) [] raw.functions (payloads 3#u8 sections)
  tables : Field (VecEncoding TableTypeEncoding) [] raw.tables (payloads 4#u8 sections)
  memories : Field (VecEncoding MemTypeEncoding) [] raw.memories (payloads 5#u8 sections)
  globals : Field (VecEncoding GlobalEncoding) [] raw.globals (payloads 6#u8 sections)
  exports : Field (VecEncoding ExportEncoding) [] raw.exports (payloads 7#u8 sections)
  start : Field StartEncoding none raw.start (payloads 8#u8 sections)
  elements : Field (VecEncoding ElementEncoding) [] raw.elements (payloads 9#u8 sections)
  codes : Field (VecEncoding CodeEncoding) [] raw.codes (payloads 10#u8 sections)
  data : Field (VecEncoding DataEncoding) [] raw.data (payloads 11#u8 sections)

end SectionDecode

/-- Erase payload interpretations to a common, uniquely framed section list. -/
theorem ModuleEncoding.sections {raw bytes} (h : ModuleEncoding raw bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections (bytes.drop magicVersion.length) ∧
      SectionDecode.Fields raw sections := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hb⟩ := h
  obtain ⟨s1, p1, hr1, hf1, hl1⟩ := h1.frames
  obtain ⟨s2, p2, hr2, hf2, hl2⟩ := h2.frames
  obtain ⟨s3, p3, hr3, hf3, hl3⟩ := h3.frames
  obtain ⟨s4, p4, hr4, hf4, hl4⟩ := h4.frames
  obtain ⟨s5, p5, hr5, hf5, hl5⟩ := h5.frames
  obtain ⟨s6, p6, hr6, hf6, hl6⟩ := h6.frames
  obtain ⟨s7, p7, hr7, hf7, hl7⟩ := h7.frames
  obtain ⟨s8, p8, hr8, hf8, hl8⟩ := h8.frames
  obtain ⟨s9, p9, hr9, hf9, hl9⟩ := h9.frames
  obtain ⟨s10, p10, hr10, hf10, hl10⟩ := h10.frames
  obtain ⟨s11, p11, hr11, hf11, hl11⟩ := h11.frames
  obtain ⟨sc, hrc, hlc⟩ := h12.frames
  let sections := s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ s10 ++ s11 ++ sc
  have hr : Rep SectionDecode.Encoding sections
      (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ b10 ++ b11 ++ b12) :=
    (((((((((((hr1.append hr2).append hr3).append hr4).append hr5).append hr6).append hr7).append hr8).append hr9).append hr10).append hr11).append hrc)
  have lookup (id : U8) (hid : id ≠ 0#u8) :
      SectionDecode.payloads id sections =
        (if id = 1#u8 then p1 else []) ++
        (if id = 2#u8 then p2 else []) ++
        (if id = 3#u8 then p3 else []) ++
        (if id = 4#u8 then p4 else []) ++
        (if id = 5#u8 then p5 else []) ++
        (if id = 6#u8 then p6 else []) ++
        (if id = 7#u8 then p7 else []) ++
        (if id = 8#u8 then p8 else []) ++
        (if id = 9#u8 then p9 else []) ++
        (if id = 10#u8 then p10 else []) ++
        (if id = 11#u8 then p11 else []) := by
    simp only [sections, SectionDecode.payloads_append, hl1 id hid, hl2 id hid, hl3 id hid,
      hl4 id hid, hl5 id hid, hl6 id hid, hl7 id hid, hl8 id hid, hl9 id hid, hl10 id hid,
      hl11 id hid, hlc id hid, List.append_nil]
  refine ⟨sections, ?_, ?_⟩
  · simpa only [hb, List.append_assoc, List.drop_left] using hr
  · constructor
    · simpa [lookup 1#u8 (by decide)] using hf1
    · simpa [lookup 2#u8 (by decide)] using hf2
    · simpa [lookup 3#u8 (by decide)] using hf3
    · simpa [lookup 4#u8 (by decide)] using hf4
    · simpa [lookup 5#u8 (by decide)] using hf5
    · simpa [lookup 6#u8 (by decide)] using hf6
    · simpa [lookup 7#u8 (by decide)] using hf7
    · simpa [lookup 8#u8 (by decide)] using hf8
    · have he : ElementEncodingFor .Wasm1 = ElementEncoding := by funext entry bytes; rfl
      rw [he] at hf9
      simpa [lookup 9#u8 (by decide)] using hf9
    · simpa [lookup 10#u8 (by decide)] using hf10
    · have he : DataEncodingFor .Wasm1 = DataEncoding := by funext entry bytes; rfl
      rw [he] at hf11
      simpa [lookup 11#u8 (by decide)] using hf11

/-- Raw modules have a unique decoding, independently of typing and implementation caps.
Custom-section placement and omitted empty fields do not introduce ambiguity. -/
theorem ModuleEncoding.unique {x y bytes}
    (hx : ModuleEncoding x bytes) (hy : ModuleEncoding y bytes) : x = y := by
  obtain ⟨xs, hxs, hxf⟩ := hx.sections
  obtain ⟨ys, hys, hyf⟩ := hy.sections
  have he := SectionDecode.unique hxs hys
  subst ys
  have h_types := SectionDecode.Field.unique funcType_prefix_unique.vec.unique hxf.types hyf.types
  have h_imports := SectionDecode.Field.unique import_prefix_unique.vec.unique hxf.imports hyf.imports
  have h_functions := SectionDecode.Field.unique index_prefix_unique.vec.unique hxf.functions hyf.functions
  have h_tables := SectionDecode.Field.unique tableType_prefix_unique.vec.unique hxf.tables hyf.tables
  have h_memories := SectionDecode.Field.unique memType_prefix_unique.vec.unique hxf.memories hyf.memories
  have h_globals := SectionDecode.Field.unique global_prefix_unique.vec.unique hxf.globals hyf.globals
  have h_exports := SectionDecode.Field.unique export_prefix_unique.vec.unique hxf.exports hyf.exports
  have h_start := SectionDecode.Field.unique start_prefix_unique.unique hxf.start hyf.start
  have h_elements := SectionDecode.Field.unique element_prefix_unique.vec.unique hxf.elements hyf.elements
  have h_codes := SectionDecode.Field.unique code_prefix_unique.vec.unique hxf.codes hyf.codes
  have h_data := SectionDecode.Field.unique data_prefix_unique.vec.unique hxf.data hyf.data
  cases x; cases y; simp_all

end Itasca.ModuleBinary
