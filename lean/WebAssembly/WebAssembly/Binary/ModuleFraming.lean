import WebAssembly.Binary.ModuleUnique

namespace WebAssembly.Binary
def EncodingUnique {α : Type} (R : α → List UInt8 → Prop) : Prop :=
  ∀ ⦃x y bytes⦄, R x bytes → R y bytes → x = y

/-- Prefix uniqueness implies uniqueness. -/
theorem PrefixUnique.unique {α : Type} {R : α → List UInt8 → Prop}
    (h : PrefixUnique R) : EncodingUnique R := by
  intro x y bytes hx hy
  exact (h hx hy (rest := []) (tail := []) rfl).1

/-- A prefix-unique relation with nonempty encodings gives unique sequence encodings. -/
theorem PrefixUnique.rep_unique {α : Type} {R : α → List UInt8 → Prop}
    (h : PrefixUnique R) (hn : ∀ x bs, R x bs → bs ≠ []) : EncodingUnique (Rep R) := by
  intro xs ys bytes hx hy
  generalize he : bytes = other at hy
  induction hx generalizing ys other with
  | nil =>
    cases hy with
    | nil => rfl
    | @cons y ys a b ha hb =>
      exact False.elim (hn y a ha (List.append_eq_nil_iff.mp he.symm).1)
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil =>
      exact False.elim (hn x a ha (List.append_eq_nil_iff.mp he).1)
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, rfl⟩ := h ha hc he
      exact congrArg (List.cons x) (ih b rfl hd)

theorem Rep.concat {α β : Type} {R : α → List β → Prop} {xs ys bs cs}
    (h : Rep R xs bs) (h' : Rep R ys cs) : Rep R (xs ++ ys) (bs ++ cs) := by
  induction h with
  | nil => simpa using h'
  | cons hx _ ih => simpa [List.append_assoc] using WebAssembly.Binary.Rep.cons hx ih

/-- `Rep` is closed under appending one entry. -/
theorem Rep.concat_one {α β : Type} {R : α → List β → Prop} {xs x bs last}
    (h : Rep R xs bs) (h' : R x last) : Rep R (xs ++ [x]) (bs ++ last) := by
  simpa using h.concat (.cons h' .nil)

theorem ValueTypeEncoding.prefix_unique : PrefixUnique ValueTypeEncoding := by
  rintro x y a b rest tail ⟨u, rfl, rfl⟩ ⟨v, rfl, rfl⟩ eq
  obtain ⟨hv, rfl⟩ := List.cons.inj eq
  have same : u = v := by cases u <;> cases v <;> first | rfl | contradiction
  subst v
  exact ⟨rfl, rfl, rfl⟩

theorem FuncTypeEncoding.prefix_unique : PrefixUnique FuncTypeEncoding := by
  rintro ⟨⟨xs⟩, ⟨ys⟩⟩ ⟨⟨us⟩, ⟨vs⟩⟩ a b rest tail ⟨p, r, hp, hr, rfl⟩ ⟨q, s, hq, hs, rfl⟩ eq
  obtain ⟨rfl, rfl, suffix⟩ := ValueTypeEncoding.prefix_unique.vec hp hq (by simpa [List.append_assoc] using (List.cons.inj eq).2)
  obtain ⟨rfl, rfl, rfl⟩ := ValueTypeEncoding.prefix_unique.vec hr hs suffix
  exact ⟨rfl, rfl, rfl⟩

theorem StartEncoding.prefix_unique : PrefixUnique StartEncoding := by
  rintro x y a b rest tail ⟨i, rfl, hi⟩ ⟨j, rfl, hj⟩ eq
  obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hi hj eq
  exact ⟨rfl, rfl, rfl⟩

namespace SectionDecode

/-- A raw section: id byte, LEB128 size and payload bytes, with the payload uninterpreted. -/
def Encoding (frame : UInt8 × List UInt8) (bytes : List UInt8) : Prop :=
  ∃ size, Leb128.U32Encoding size frame.2.length ∧ bytes = frame.1 :: (size ++ frame.2)

/-- Raw section frames are prefix-unique. -/
theorem prefix_unique : PrefixUnique Encoding := by
  rintro ⟨xt, xp⟩ ⟨yt, yp⟩ a b rest tail ⟨xn, hx, rfl⟩ ⟨yn, hy, rfl⟩ he
  obtain ⟨rfl, hbody⟩ := List.cons.inj he
  obtain ⟨hlen, rfl, hpayload⟩ := IndexEncoding.prefix_unique hx hy
    (by simpa [List.append_assoc] using hbody)
  obtain ⟨rfl, rfl⟩ := split_of_length hpayload hlen
  exact ⟨rfl, rfl, rfl⟩

/-- A sequence of raw section frames is determined by its bytes. -/
theorem unique : EncodingUnique (Rep Encoding) :=
  prefix_unique.rep_unique (by rintro _ _ ⟨n, hn, rfl⟩; simp)

/-- The payloads of the sections with the given id, in order. -/
def payloads (id : UInt8) : List (UInt8 × List UInt8) → List (List UInt8)
  | [] => []
  | (tag, bytes) :: sections =>
      if id = tag then bytes :: payloads id sections else payloads id sections

theorem payloads_append (id : UInt8) (xs ys : List (UInt8 × List UInt8)) :
    payloads id (xs ++ ys) = payloads id xs ++ payloads id ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [List.cons_append, payloads]; split <;> simp_all

/-- A standard field is either omitted, giving `absent`, or encoded by exactly one payload. -/
inductive Field {α : Type} (R : α → List UInt8 → Prop) (absent : α) : α → List (List UInt8) → Prop where
  | absent : Field R absent absent []
  | present {value bytes} : R value bytes → Field R absent value [bytes]

/-- A field's value is determined by its payloads. -/
theorem Field.unique {α : Type} {R : α → List UInt8 → Prop} {absent x y payloads}
    (hu : EncodingUnique R) (hx : Field R absent x payloads) (hy : Field R absent y payloads) : x = y := by
  cases hx <;> cases hy
  · rfl
  · apply hu <;> assumption

end SectionDecode

/-- A section encoding gives a raw frame with the same payload. -/
theorem SectionEncoding.frame {α : Type} {R : α → List UInt8 → Prop} {id value bytes}
    (h : SectionEncoding id R value bytes) :
    ∃ payload, R value payload ∧ SectionDecode.Encoding (id, payload) bytes := by
  obtain ⟨size, payload, hn, hp, rfl⟩ := h
  exact ⟨payload, hp, size, hn, rfl⟩

/-- Custom sections frame into a section list with no payload for any other id. -/
theorem CustomsEncoding.frames {bytes} (h : CustomsEncoding bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections bytes ∧
      ∀ id, id ≠ 0 → SectionDecode.payloads id sections = [] := by
  induction h with
  | nil => exact ⟨[], .nil, by intros; rfl⟩
  | cons hc _ ih =>
    obtain ⟨nm, content, nameBytes, hn, hs⟩ := hc
    obtain ⟨payload, _, hf⟩ := SectionEncoding.frame hs
    obtain ⟨sections, hp, hids⟩ := ih
    refine ⟨(0, payload) :: sections, .cons hf hp, ?_⟩
    intro id hid
    simp [SectionDecode.payloads, hid, hids id hid]

/-- A field preceded by custom sections frames into a section list with the field's payload
under its own id and none under other ids. -/
theorem PaddedEncoding.frames {α : Type} {R : α → List UInt8 → Prop} {id absent value bytes}
    (h : PaddedEncoding id R absent value bytes) :
    ∃ sections payloads, Rep SectionDecode.Encoding sections bytes ∧
      SectionDecode.Field R absent value payloads ∧
      ∀ wanted, wanted ≠ 0 → SectionDecode.payloads wanted sections =
        if wanted = id then payloads else [] := by
  obtain ⟨customs, sec, hc, hs, rfl⟩ := h
  obtain ⟨before, hp, hids⟩ := CustomsEncoding.frames hc
  cases hs with
  | absent => exact ⟨before, [], by simpa using hp, .absent, by intros; simp [*]⟩
  | present hs =>
    obtain ⟨payload, hv, hf⟩ := SectionEncoding.frame hs
    refine ⟨before ++ [(id, payload)], [payload], hp.concat_one hf, .present hv, ?_⟩
    intro wanted hw
    simp [SectionDecode.payloads_append, hids wanted hw, SectionDecode.payloads]

/-- The data count section frames like other optional fields. -/
theorem DataCountSectionEncoding.frames {value bytes}
    (h : DataCountSectionEncoding value bytes) :
    ∃ sections payloads, Rep SectionDecode.Encoding sections bytes ∧
      SectionDecode.Field StartEncoding none value payloads ∧
      ∀ wanted, wanted ≠ 0 → SectionDecode.payloads wanted sections =
        if wanted = 12 then payloads else [] := by
  exact PaddedEncoding.frames h

namespace SectionDecode

/-- The standard fields of a raw module as payloads of a raw section list. -/
structure Fields (raw : Module) (sections : List (UInt8 × List UInt8))
    (codeRel : Code → List UInt8 → Prop) : Prop where
  types : Field (VecEncoding FuncTypeEncoding) [] raw.types (payloads 1 sections)
  imports : Field (VecEncoding ImportEncoding) [] raw.imports (payloads 2 sections)
  functions : Field (VecEncoding IndexEncoding) [] raw.functions (payloads 3 sections)
  tables : Field (VecEncoding TableTypeEncoding) [] raw.tables (payloads 4 sections)
  memories : Field (VecEncoding MemTypeEncoding) [] raw.memories (payloads 5 sections)
  globals : Field (VecEncoding GlobalEncoding) [] raw.globals (payloads 6 sections)
  exports : Field (VecEncoding ExportEncoding) [] raw.exports (payloads 7 sections)
  start : Field StartEncoding none raw.start (payloads 8 sections)
  elements : Field (VecEncoding ElementEncoding) [] raw.elements (payloads 9 sections)
  dataCount : Field StartEncoding none raw.dataCount (payloads 12 sections)
  codes : Field (VecEncoding codeRel) [] raw.codes (payloads 10 sections)
  data : Field (VecEncoding DataEncoding) [] raw.data (payloads 11 sections)

end SectionDecode

/-- A module encoding gives a raw section list that carries every standard field. -/
theorem ModuleEncodingWith.sections {codeRel raw bytes}
    (h : ModuleEncodingWith codeRel raw bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections (bytes.drop magicVersion.length) ∧
      SectionDecode.Fields raw sections codeRel := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, bc, b10, b11, b12,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, hc, h10, h11, h12, hb, _⟩ := h
  obtain ⟨s1, p1, hr1, hf1, hl1⟩ := PaddedEncoding.frames h1
  obtain ⟨s2, p2, hr2, hf2, hl2⟩ := PaddedEncoding.frames h2
  obtain ⟨s3, p3, hr3, hf3, hl3⟩ := PaddedEncoding.frames h3
  obtain ⟨s4, p4, hr4, hf4, hl4⟩ := PaddedEncoding.frames h4
  obtain ⟨s5, p5, hr5, hf5, hl5⟩ := PaddedEncoding.frames h5
  obtain ⟨s6, p6, hr6, hf6, hl6⟩ := PaddedEncoding.frames h6
  obtain ⟨s7, p7, hr7, hf7, hl7⟩ := PaddedEncoding.frames h7
  obtain ⟨s8, p8, hr8, hf8, hl8⟩ := PaddedEncoding.frames h8
  obtain ⟨s9, p9, hr9, hf9, hl9⟩ := PaddedEncoding.frames h9
  obtain ⟨sCount, pCount, hrCount, hfCount, hlCount⟩ := DataCountSectionEncoding.frames hc
  obtain ⟨s10, p10, hr10, hf10, hl10⟩ := PaddedEncoding.frames h10
  obtain ⟨s11, p11, hr11, hf11, hl11⟩ := PaddedEncoding.frames h11
  obtain ⟨sc, hrc, hlc⟩ := CustomsEncoding.frames h12
  let sections := s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ sCount ++ s10 ++ s11 ++ sc
  have hr : Rep SectionDecode.Encoding sections
      (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ bc ++ b10 ++ b11 ++ b12) :=
    ((((((((((((hr1.concat hr2).concat hr3).concat hr4).concat hr5).concat hr6).concat hr7).concat hr8).concat hr9).concat hrCount).concat hr10).concat hr11).concat hrc)
  have lookup (id : UInt8) (hid : id ≠ 0) :
      SectionDecode.payloads id sections =
        (if id = 1 then p1 else []) ++
        (if id = 2 then p2 else []) ++
        (if id = 3 then p3 else []) ++
        (if id = 4 then p4 else []) ++
        (if id = 5 then p5 else []) ++
        (if id = 6 then p6 else []) ++
        (if id = 7 then p7 else []) ++
        (if id = 8 then p8 else []) ++
        (if id = 9 then p9 else []) ++
        (if id = 12 then pCount else []) ++
        (if id = 10 then p10 else []) ++
        (if id = 11 then p11 else []) := by
    simp only [sections, SectionDecode.payloads_append, hl1 id hid, hl2 id hid, hl3 id hid,
      hl4 id hid, hl5 id hid, hl6 id hid, hl7 id hid, hl8 id hid, hl9 id hid, hlCount id hid, hl10 id hid,
      hl11 id hid, hlc id hid, List.append_nil, id_eq] <;> rfl
  refine ⟨sections, ?_, ?_⟩
  · simpa only [hb, List.map_id_fun, id_eq, List.append_assoc, List.drop_left] using hr
  · constructor
    · simpa (config := { decide := true }) [lookup 1 (by decide)] using hf1
    · simpa (config := { decide := true }) [lookup 2 (by decide)] using hf2
    · simpa (config := { decide := true }) [lookup 3 (by decide)] using hf3
    · simpa (config := { decide := true }) [lookup 4 (by decide)] using hf4
    · simpa (config := { decide := true }) [lookup 5 (by decide)] using hf5
    · simpa (config := { decide := true }) [lookup 6 (by decide)] using hf6
    · simpa (config := { decide := true }) [lookup 7 (by decide)] using hf7
    · simpa (config := { decide := true }) [lookup 8 (by decide)] using hf8
    · simpa (config := { decide := true }) [lookup 9 (by decide)] using hf9
    · simpa (config := { decide := true }) [lookup 12 (by decide)] using hfCount
    · simpa (config := { decide := true }) [lookup 10 (by decide)] using hf10
    · simpa (config := { decide := true }) [lookup 11 (by decide)] using hf11

/-- A byte string encodes at most one raw module, with no typing or implementation limit premise. -/
theorem ModuleEncodingWith.unique {codeRel x y bytes}
    (hcode : PrefixUnique codeRel)
    (hx : ModuleEncodingWith codeRel x bytes)
    (hy : ModuleEncodingWith codeRel y bytes) : x = y := by
  obtain ⟨xs, hxs, hxf⟩ := hx.sections
  obtain ⟨ys, hys, hyf⟩ := hy.sections
  have he := SectionDecode.unique hxs hys
  subst ys
  have h_types := SectionDecode.Field.unique FuncTypeEncoding.prefix_unique.vec.unique hxf.types hyf.types
  have h_imports := SectionDecode.Field.unique ImportEncoding.prefix_unique.vec.unique hxf.imports hyf.imports
  have h_functions := SectionDecode.Field.unique IndexEncoding.prefix_unique.vec.unique hxf.functions hyf.functions
  have h_tables := SectionDecode.Field.unique TableTypeEncoding.prefix_unique.vec.unique hxf.tables hyf.tables
  have h_memories := SectionDecode.Field.unique MemTypeEncoding.prefix_unique.vec.unique hxf.memories hyf.memories
  have h_globals := SectionDecode.Field.unique GlobalEncoding.prefix_unique.vec.unique hxf.globals hyf.globals
  have h_exports := SectionDecode.Field.unique ExportEncoding.prefix_unique.vec.unique hxf.exports hyf.exports
  have h_start := SectionDecode.Field.unique StartEncoding.prefix_unique.unique hxf.start hyf.start
  have h_elements := SectionDecode.Field.unique ElementEncoding.prefix_unique.vec.unique hxf.elements hyf.elements
  have h_count := SectionDecode.Field.unique StartEncoding.prefix_unique.unique hxf.dataCount hyf.dataCount
  have h_codes := SectionDecode.Field.unique hcode.vec.unique hxf.codes hyf.codes
  have h_data := SectionDecode.Field.unique DataEncoding.prefix_unique.vec.unique hxf.data hyf.data
  cases x; cases y; simp_all


end WebAssembly.Binary
