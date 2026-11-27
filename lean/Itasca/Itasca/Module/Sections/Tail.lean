import Itasca.Module.Elab.SegmentTyping
import Itasca.Module.Const.Parser
import Itasca.Module.Readers.Completeness
import Itasca.Stream.Definitions

/-! ## Data -/

section

/-!
# Data section parser

Soundness of `metadata.decode_data_segment`, `metadata.decode_data_section_loop` and
`metadata.decode_data_section`. Accepted segments are spans of the independent grammar
(`DataEncoding`) and satisfy `Module.Data.Valid`,
which covers the memory index and the offset initializer of active segments. Completeness is in `Module/Sections/TailComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Data

/-- A repetition span extends by one segment at its end. -/
theorem at_snoc {R : Binary.Data → List U8 → Prop} {data start pos next values value}
    (h : Binary.At (Binary.Rep R) data start values pos)
    (h' : Binary.At R data pos value next) :
    Binary.At (Binary.Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- Like `encoded`: a flag word and the index encoding give an active
`DataEncoding`. -/
theorem encoded {data start first p1 p2 p3 next flags memory explicit offset count init}
    (hf : Binary.Leb128.Decoded data start flags first)
    (hm : Binary.At (fun pair => Binary.SegmentIndexEncoding flags pair.1 pair.2)
      data first (memory, explicit) p1)
    (ho : Binary.At Binary.ConstEncoding data p1 offset p2)
    (hc : Binary.Leb128.Decoded data p2 count p3)
    (hi : Body.Scalar.BytesAt data p3 init next) (hlen : init.length = count.val) :
    Binary.At Binary.DataEncoding data start
      ⟨.Active memory offset, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := Binary.At.of_u32 hf
  obtain ⟨mb, hm, hms⟩ := hm
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hspan : Body.Scalar.BytesAt data p2 cb p3 := ⟨hcs, hcl, hcb⟩
  refine ⟨fb ++ mb ++ ob ++ (cb ++ init), ?_, ?_⟩
  · apply Binary.DataEncoding.of_parts hf hm ho
    exact Binary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩
  · exact ((hfs.append hms).append hos).append (hspan.append hi)

/-- Flag `1` followed by a counted byte string is a passive Wasm 2.0 data segment. -/
theorem passive_encoded {data start first content next count init}
    (hf : Binary.Leb128.Decoded data start 1#u32 first)
    (hc : Binary.Leb128.Decoded data first count content)
    (hi : Body.Scalar.BytesAt data content init next) (hlen : init.length = count.val) :
    Binary.At Binary.DataEncoding data start ⟨.Passive, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := Binary.At.of_u32 hf
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hcount : Body.Scalar.BytesAt data first cb content := ⟨hcs, hcl, hcb⟩
  exact ⟨fb ++ (cb ++ init), Binary.DataEncoding.of_passive hf
    (Binary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩),
    hfs.append (hcount.append hi)⟩

end Itasca.Module.Data

namespace Itasca

/-- An accepted `metadata.decode_data_segment` is a `DataEncoding` span and its segment
is `Module.Data.Valid`. -/
@[step]
theorem metadata.decode_data_segment.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata) :
    metadata.decode_data_segment data pos env ⦃ r => match r with
      | .Ok (segment, next) =>
          Binary.At Binary.DataEncoding data pos (Module.Data.raw segment) next ∧
          Module.Data.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_segment, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨flags, first⟩
    change Binary.Leb128.Decoded data pos flags first at hm
    by_cases hpass : flags = 1#u32
    · subst flags
      obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
      cases r with
      | Err e => simp [metadata.decode_data_segment, hr, hlen, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨count, content⟩ := pair
        simp [metadata.decode_data_segment, hr, hlen, core.result.Result.Insts.CoreOpsTry.branch]
        step
        have hcontent : content.val ≤ data.length := hc.span.2.2
        obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hcontent)
        cases r with
        | Err e => simp [hh, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
          cases u
          simp only [hh, bind_ok]
          have havail' : content.val + n.val ≤ data.length := havail.1.mp rfl
          step
          step
          refine ⟨Module.Data.passive_encoded hm hc init_post ?_, trivial⟩
          have hl := init_post.length
          scalar_tac
    ·
      obtain ⟨r, hseg, hindex⟩ := WP.spec_imp_exists
        (metadata.decode_segment_index.spec data first flags hm.span.2.2)
      cases r with
      | Err e =>
          simp [metadata.decode_data_segment, hr, hseg, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          split <;> first | contradiction | simp
      | Ok triple =>
          obtain ⟨memory, p1, explicit⟩ := triple
          simp [metadata.decode_data_segment, hr, hseg, core.result.Result.Insts.CoreOpsTry.branch]
          split <;> try contradiction
          step
          split
          · simp
          · have hmem : memory.val < env.memories.val.length := by scalar_tac
            obtain ⟨r, hr, ho⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data p1 env .I32)
            cases r with
            | Err e =>
              simp [hr, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
              rcases pair with ⟨offset, p2⟩
              change Binary.At Binary.ConstEncoding data p1 offset p2 ∧
                Module.Constants.Valid env offset .I32 at ho
              obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p2)
              cases r with
              | Err e =>
                simp [hr, hlen, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                rcases pair with ⟨count, p3⟩
                change Binary.Leb128.Decoded data p2 count p3 at hc
                simp [hr, hlen]
                step
                have hp3 : p3.val ≤ data.length := hc.span.2.2
                obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data p3 n hp3)
                cases r with
                | Err e =>
                  simp [hh, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok u =>
                  cases u
                  simp only [hh, bind_ok]
                  have havail' : p3.val + n.val ≤ data.length := havail.1.mp rfl
                  step
                  step
                  refine ⟨Module.Data.encoded hm hindex ho.1 hc init_post ?_, hmem, ho.2⟩
                  have hl := init_post.length
                  scalar_tac

/-- The data loop returns `count` segments forming a `Rep` span, all valid. -/
@[step]
theorem metadata.decode_data_section_loop.spec (data : Slice U8) (env : metadata.CodeMetadata)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    metadata.decode_data_section_loop data env count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (segments, next) => segments.val.length = count.val ∧
          Binary.At (Binary.Rep Binary.DataEncoding)
            data start (segments.val.map Module.Data.raw) next ∧
          ∀ segment ∈ segments.val, Module.Data.Valid env segment
      | .Err _ => True ⦄ := by
  unfold metadata.decode_data_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      Binary.At (Binary.Rep Binary.DataEncoding)
        data start (s.1.val.map Module.Data.raw) s.2.1 ∧
      ∀ segment ∈ s.1.val, Module.Data.Valid env segment)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hbytes, hvalid⟩
    dsimp only at hi hlen hbytes hvalid
    unfold metadata.decode_data_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, hbytes, hvalid⟩
    · rename_i hmore
      have hlt : i.val < count.val := by scalar_tac
      have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_data_segment.spec data pos env)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        rcases pair with ⟨segment, next⟩
        obtain ⟨hb, ht⟩ := hp
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        step
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · scalar_tac
        · simp only [out1_post, List.length_append, List.length_singleton]
          scalar_tac
        · simpa [out1_post, List.map_append] using Module.Data.at_snoc hbytes hb
        · intro entry he
          rw [out1_post] at he
          rcases List.mem_append.mp he with he | he
          · exact hvalid entry he
          · simpa [List.mem_singleton.mp he] using ht
        · scalar_tac
  · refine ⟨by simp, by simp, ?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩

/-- An accepted `metadata.decode_data_section` returns segments forming a `VecEncoding` span, all
valid. -/
@[step]
theorem metadata.decode_data_section.spec (data : Slice U8) (pos : Usize) (env : metadata.CodeMetadata) :
    metadata.decode_data_section data pos env ⦃ r => match r with
      | .Ok (segments, next) =>
          Binary.At (Binary.VecEncoding Binary.DataEncoding)
            data pos (segments.val.map Module.Data.raw) next ∧
          ∀ segment ∈ segments.val, Module.Data.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨count, start⟩
    change Binary.Leb128.Decoded data pos count start at hc
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_data_section_loop.spec data env count start hc.span.2.2)
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok pair =>
      rcases pair with ⟨segments, next⟩
      obtain ⟨hlen, hbytes, hvalid⟩ := hp
      obtain ⟨bytes, he, hs⟩ := hbytes
      obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
      have hcspan : Body.Scalar.BytesAt data pos countBytes start := ⟨hcs, hcl, hcb⟩
      refine ⟨⟨countBytes ++ bytes, ?_, hcspan.append hs⟩, hvalid⟩
      exact ⟨countBytes, bytes, by simpa [hlen] using hce, he, rfl⟩

end Itasca

end
/-! ## Tail -/

section

/-!
# Module tail parser

The tail is the input after the code section: custom sections, at most one data section, then
custom sections, running to EOF. `Module.Tail.Encoding` is its independent grammar and `Prefix` the
invariant of the parsing loop. `metadata.validate_tail_with.spec` shows that an accepted tail is an
`Encoding` span to EOF whose segments are valid and agree with the data count, for any visitor
whose custom-section hook returns normally (`HooksTotal`). `metadata.validate_tail.spec` is the
specialization to the empty visitor. Completeness is in `Module/Sections/TailComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Tail

open Binary

/-- Custom section sequences concatenate. -/
theorem customs_append {xs ys} (hx : CustomsEncoding xs) (hy : CustomsEncoding ys) :
    CustomsEncoding (xs ++ ys) := by
  induction hx with
  | nil => simpa using hy
  | cons h _ ih => simpa [List.append_assoc] using WebAssembly.Binary.CustomsEncodingWith.cons h ih

/-- The loop invariant: the bytes so far are custom sections plus at most one data section whose
segments are listed. The flag records whether the data section has occurred. -/
inductive Prefix :
    Bool → List Binary.Data → List U8 → Prop where
  | empty : Prefix false [] []
  | custom {seen segments before bytes} : Prefix seen segments before →
      CustomEncoding bytes → Prefix seen segments (before ++ bytes)
  | data {before bytes segments} : Prefix false [] before →
      SectionEncoding 11#u8 (VecEncoding DataEncoding) segments bytes →
      Prefix true segments (before ++ bytes)

/-- Before the data section, a prefix has no segments and is only custom sections. -/
theorem Prefix.not_seen {seen segments bytes} (h : Prefix seen segments bytes)
    (hs : seen = false) : segments = [] ∧ CustomsEncoding bytes := by
  induction h with
  | empty => exact ⟨rfl, .nil⟩
  | custom _ hc ih =>
    obtain ⟨he, hp⟩ := ih hs
    exact ⟨he, by simpa using customs_append hp (.cons hc .nil)⟩
  | data => cases hs

/-- The independent grammar of the tail: padded data section (custom sections, then an optional
data section) followed by custom sections. -/
def Encoding (segments : List Binary.Data) (bytes : List U8) : Prop :=
  ∃ chunk customs, PaddedEncoding 11#u8 (VecEncoding DataEncoding) [] segments chunk ∧
    CustomsEncoding customs ∧ bytes = chunk ++ customs

/-- A prefix is a tail encoding. -/
theorem Prefix.encoding {seen segments bytes} (h : Prefix seen segments bytes) :
    Encoding segments bytes := by
  induction h with
  | empty => exact ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩
  | custom _ hc ih =>
    obtain ⟨chunk, customs, hs, ht, he⟩ := ih
    exact ⟨chunk, _, hs, (by simpa using customs_append ht (.cons hc .nil)), by simp [he, List.append_assoc]⟩
  | data hp hd =>
    exact ⟨_, [], ⟨_, _, (hp.not_seen rfl).2, .present hd, rfl⟩, .nil, by simp⟩

/-- A section header and its payload span form a section encoding. -/
theorem header_payload {α : Type} {R : α → List U8 → Prop} {data start id first last value}
    (hh : SectionHeader data start id first last)
    (hp : At R data first value last) :
    At (SectionEncoding id R) data start value last := by
  obtain ⟨pos, size, hb, hd, he, hend⟩ := hh
  obtain ⟨payload, hp, hs⟩ := hp
  obtain ⟨sizeBytes, hd, hl, hn, hc⟩ := hd
  have hlen : payload.length = size.val := by have := hs.length; omega
  have hsize : Body.Scalar.BytesAt data pos sizeBytes first := ⟨hd, hl, hn⟩
  refine ⟨id :: (sizeBytes ++ payload), ⟨sizeBytes, payload, ?_, hp, rfl⟩, ?_⟩
  · simpa [hlen] using hc
  · simpa using hb.byte.append (hsize.append hs)

/-- A custom section header and a name within it form a `CustomEncoding` span. -/
theorem custom_encoded {data start first last nm} {custom : wasm_types.CustomSection}
    (hh : SectionHeader data start 0#u8 first last)
    (hn : At NameEncoding data first nm custom.payload_start)
    (hp : custom.payload_start.val ≤ last.val) :
    At (fun (_ : Unit) => CustomEncoding) data start () last := by
  obtain ⟨payload, _, hs⟩ := WP.spec_imp_exists
    (metadata.copy_bytes.spec data custom.payload_start last hp hh.span.2.2)
  obtain ⟨nameBytes, hn, hns⟩ := hn
  have hpayload : At (fun (_ : Unit) bs => bs = nameBytes ++ payload.val) data first () last :=
    ⟨nameBytes ++ payload.val, rfl, hns.append hs⟩
  obtain ⟨bytes, he, hb⟩ := header_payload hh hpayload
  exact ⟨bytes, ⟨nm, payload.val, nameBytes, hn, he⟩, hb⟩

/-- A custom section extends a tail prefix. -/
theorem append_custom {seen segments data start pos next}
    (hp : At (fun segments bytes => Prefix seen segments bytes) data start segments pos)
    (hc : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    At (fun segments bytes => Prefix seen segments bytes) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hc, ht⟩ := hc
  exact ⟨before ++ bytes, .custom hp hc, hs.append ht⟩

/-- A data section extends a prefix that has not seen one. -/
theorem append_data {old segments data start pos next}
    (hp : At (fun segments bytes => Prefix false segments bytes) data start old pos)
    (hd : At (SectionEncoding 11#u8 (VecEncoding DataEncoding)) data pos segments next) :
    At (fun segments bytes => Prefix true segments bytes) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hd, ht⟩ := hd
  have he := (hp.not_seen rfl).1
  subst old
  exact ⟨before ++ bytes, .data hp hd, hs.append ht⟩

/-- The empty module visitor has total hooks. -/
theorem empty_hooks_total : HooksTotal metadata.DefaultModuleVisitor.Insts.ItascaMetadataModuleVisitor := by
  intro v chunk
  exact ⟨(.Ok (), v), rfl⟩

end Itasca.Module.Tail

namespace Itasca

/-- `metadata.validate_tail_with` consumes the input to EOF as custom sections around at most one data
section. An accepted tail is an `Encoding` span with valid segments that agree with the data
count. Hooks may reject. -/
theorem metadata.validate_tail_with.spec {V : Type} (visitor : metadata.ModuleVisitor V)
    (htotal : Module.Tail.HooksTotal visitor) (data : Slice U8) (start : Usize)
    (env : metadata.CodeMetadata) (v : V) (hstart : start.val ≤ data.length) :
    metadata.validate_tail_with visitor data start env v ⦃ r => match r.1 with
      | .Ok tail => Binary.At (fun segments bytes => Module.Tail.Encoding segments bytes) data start
          (tail.val.map Module.Data.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.val, Module.Data.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.val.length
      | .Err _ => True ⦄ := by
  unfold metadata.validate_tail_with metadata.validate_tail_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => Binary.At (fun segments bytes => Module.Tail.Prefix s.2.2.2 segments bytes) data start
        (s.2.1.val.map Module.Data.raw) s.2.2.1 ∧
      ∀ segment ∈ s.2.1.val, Module.Data.Valid env segment)
  · rintro ⟨state, segments, pos, seen⟩ ⟨hbytes, hvalid⟩
    dsimp only at hbytes hvalid
    have hpos : pos.val ≤ data.length := hbytes.span.2
    unfold metadata.validate_tail_with_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : pos = Slice.len data := by apply UScalar.eq_of_val_eq; scalar_tac
      obtain ⟨bytes, hp, hs⟩ := hbytes
      cases hcount : env.data_count with
      | none =>
        simp only [WP.spec_ok]
        exact ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, by simp⟩
      | some count =>
        step
        split
        · simp
        · simp only [WP.spec_ok]
          refine ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, ?_⟩
          intro other ho
          have he : other = count := Option.some.inj ho.symm
          subst other
          scalar_tac
    · rename_i hmore
      have hlt : pos.val < data.length := by scalar_tac
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (metadata.read_section_header.spec data pos)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok triple =>
        rcases triple with ⟨id, first, last⟩
        change Binary.SectionHeader data pos id first last at hh
        have hspan := hh.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        by_cases hc : id = metadata.SECTION_CUSTOM
        · simp only [hc, ↓reduceIte]
          obtain ⟨r, hcustom, hp⟩ := WP.spec_imp_exists (metadata.decode_custom_section.spec data first last)
          rw [hcustom]
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, hend, _⟩ := hp
            have hb := Module.Tail.custom_encoded (by simpa [hc, metadata.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp
            | Ok u =>
              exact ⟨Module.Tail.append_custom hbytes hb, hvalid, by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          by_cases hd : id = metadata.SECTION_DATA
          · subst id
            simp only [↓reduceIte]
            cases seen with
            | true => simp
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              obtain ⟨r, hdata, hp⟩ := WP.spec_imp_exists (metadata.decode_data_section.spec data first env)
              rw [hdata]
              cases r with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok pair =>
                rcases pair with ⟨decoded, next⟩
                obtain ⟨hencoded, htyped⟩ := hp
                simp
                by_cases he : next = last
                · subst next
                  simp only [↓reduceIte, WP.spec_ok]
                  have hb := Module.Tail.header_payload hh hencoded
                  exact ⟨Module.Tail.append_data hbytes (by simpa [metadata.SECTION_DATA] using hb), htyped, by scalar_tac⟩
                · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hn]
          · have hn : id.val ≠ metadata.SECTION_DATA.val := fun h => hd (UScalar.eq_of_val_eq h)
            simp [hn]
  · refine ⟨?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .empty, Body.Scalar.BytesAt.nil data start hstart⟩

/-- `metadata.validate_tail` satisfies the same specification as `metadata.validate_tail_with`. -/
theorem metadata.validate_tail.spec (data : Slice U8) (start : Usize) (env : metadata.CodeMetadata)
    (hstart : start.val ≤ data.length) :
    metadata.validate_tail data start env ⦃ r => match r with
      | .Ok tail => Binary.At (fun segments bytes => Module.Tail.Encoding segments bytes) data start
          (tail.val.map Module.Data.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.val, Module.Data.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.val.length
      | .Err _ => True ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (metadata.validate_tail_with.spec metadata.DefaultModuleVisitor.Insts.ItascaMetadataModuleVisitor
      Module.Tail.empty_hooks_total data start env () hstart)
  simpa [metadata.validate_tail, hr] using hp

end Itasca

end
