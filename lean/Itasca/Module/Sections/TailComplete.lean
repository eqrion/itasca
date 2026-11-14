import Itasca.Module.Env.Complete
import Itasca.Module.Sections.Tail
import Itasca.Module.Env.Encoding
import Itasca.Module.Const.ParserComplete
import Itasca.Module.Readers.Utf8
import Itasca.Module.Sections.Data
import Itasca.Module.Readers.TypesComplete

/-!
Sections, each formerly its own module: DataMaterialize, DataComplete, TailComplete.
-/

/-! ## DataMaterialize -/

section

/-!
# Materializing independent data segments

Turns independently encoded data segments into runtime `metadata.Data` values without running the
parser. The counts in the binary grammar bound every vector length (`.length_bounded`), so
`DataEncodingFor.materialize` and `ModuleTail.Encoding.materialize` produce the segments, and
`ModuleTail.materialize` also shows they are `ModuleData.Valid` in the ready environment. The
tail completeness proof in `Module/Sections/TailComplete` uses these.
-/

open Aeneas Aeneas.Std alloc.vec

namespace Itasca.ModuleBinary

/-- A vector encoding has at most `Usize.max` elements, because its count is a `u32`. -/
theorem VecEncoding.length_bounded {α : Type} {R : α → List U8 → Prop}
    {values bytes} (h : VecEncoding R values bytes) : values.length ≤ Usize.max := by
  obtain ⟨_, _, hc, _, _⟩ := h
  have hn := hc.value_lt
  scalar_tac

/-- A padded vector section has at most `Usize.max` elements. -/
theorem PaddedEncoding.length_bounded {α : Type} {R : α → List U8 → Prop}
    {id values bytes} (h : PaddedEncoding id (VecEncoding R) [] values bytes) :
    values.length ≤ Usize.max := by
  obtain ⟨_, _, _, hs, _⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨_, _, _, hv, _⟩ := hp
    exact hv.length_bounded

/-- A data segment's bytes fit in `Usize`. -/
theorem DataEncodingFor.init_bounded {entry bytes}
    (h : DataEncodingFor entry bytes) : entry.init.length ≤ Usize.max := by
  cases h with
  | active _ _ hi => exact hi.length_bounded
  | passive _ hi => exact hi.length_bounded

/-- A `DataEncodingFor` entry is the raw form of some runtime `metadata.Data`. -/
theorem DataEncodingFor.materialize {entry bytes}
    (h : DataEncodingFor entry bytes) :
    ∃ segment : metadata.Data, ModuleData.raw segment = entry := by
  refine ⟨⟨entry.mode, Vec.from entry.init h.init_bounded⟩, ?_⟩
  simp [ModuleData.raw]

end Itasca.ModuleBinary

namespace Itasca.ModuleTail

open ModuleBinary

private theorem materialize_list (entries : List ModuleBinary.Data)
    (h : ∀ entry ∈ entries, ∃ bytes, DataEncodingFor entry bytes) :
    ∃ segments : List metadata.Data, segments.map ModuleData.raw = entries := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries ih =>
    obtain ⟨_, he⟩ := h entry (by simp)
    obtain ⟨segment, hs⟩ := he.materialize
    obtain ⟨segments, hss⟩ := ih (fun e hm => h e (by simp [hm]))
    exact ⟨segment :: segments, by simp [hs, hss]⟩

/-- A tail encoding's segments are the raw form of some runtime vector of `metadata.Data`. The
allocation bounds come from the data count and each segment's byte count, and no parser
acceptance is assumed. -/
theorem Encoding.materialize {entries bytes} (h : Encoding entries bytes) :
    ∃ segments : Vec metadata.Data, segments.val.map ModuleData.raw = entries := by
  obtain ⟨_, _, hp, _, _⟩ := h
  obtain ⟨segments, hs⟩ := materialize_list entries (fun entry hm => hp.member hm)
  have hn : segments.length ≤ Usize.max := by
    have := hp.length_bounded
    simpa [← hs] using this
  exact ⟨Vec.from segments hn, by simpa using hs⟩

end Itasca.ModuleTail

namespace Itasca.ModuleEnv

open ModuleElaboration

/-- Segments matching typed raw data are `ModuleData.Valid` in a ready environment. -/
theorem Ready.data_valid {raw decls env} (hready : Ready raw 10 decls env)
    (htyped : SectionsTyped raw) {segments : Vec metadata.Data}
    (hmap : segments.val.map ModuleData.raw = raw.data) :
    ∀ segment ∈ segments.val, ModuleData.Valid env segment := by
  intro segment hm
  have hr : ModuleData.raw segment ∈ raw.data := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨segment, hm, rfl⟩
  apply data_valid_of_typing (hready.initializer_globals (by decide))
  · simpa [ModuleConstants.FunctionContext, initializerContextOf] using hready.funcs_context (by decide)
  · simpa [initializerContextOf] using hready.memories_context (by decide)
  · exact htyped.data _ hr

end Itasca.ModuleEnv

namespace Itasca.ModuleTail

/-- An independently encoded tail whose sections are typed gives runtime segments that match the
raw data and are valid in the ready environment. -/
theorem materialize (data : Slice U8) (start next : Usize)
    (raw : ModuleBinary.Module) (decls : ModuleEnv.Declarations) (env : metadata.Env)
    (hb : ModuleBinary.At (fun es bs => Encoding es bs) data start raw.data next)
    (htyped : ModuleElaboration.SectionsTyped raw)
    (hready : ModuleEnv.Ready raw 10 decls env) :
    ∃ segments : Vec metadata.Data, segments.val.map ModuleData.raw = raw.data ∧
      ∀ segment ∈ segments.val, ModuleData.Valid env segment := by
  obtain ⟨_, he, _⟩ := hb
  obtain ⟨segments, hs⟩ := he.materialize
  exact ⟨segments, hs, hready.data_valid htyped hs⟩

end Itasca.ModuleTail

end

/-! ## DataComplete -/

section

/-!
# Completeness of the data section parser

`metadata.decode_data_section.profile_complete`: an independently
encoded vector of `ModuleData.Valid` segments is accepted and returned unchanged. The segment
lemmas split active and passive encodings. Soundness is in `Module/Sections/Data`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

private theorem data_active_parts {idx offset init bytes}
    (h : DataEncodingFor ⟨.Active idx offset, init⟩ bytes) :
    ∃ flags explicit fb mb ob ib, IndexEncoding flags fb ∧
      SegmentIndexEncoding flags idx explicit mb ∧ ConstEncoding offset ob ∧
      ByteVecEncoding init ib ∧ bytes = fb ++ mb ++ ob ++ ib := by
  cases h with
  | active hi ho hb =>
    obtain ⟨flags, fb, mb, hf, hm, rfl⟩ := hi.parts
    exact ⟨flags, _, fb, mb, _, _, hf, hm, ho, hb, rfl⟩

private theorem data_active_complete {data : Slice U8} {pos next : Usize}
    {env : metadata.Env} (idx : U32) (offset : wasm_types.ConstExpr) (init : alloc.vec.Vec U8)

    (hb : At (DataEncodingFor) data pos ⟨.Active idx offset, init.val⟩ next)
    (hv : idx.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32) :
    metadata.decode_data_segment data pos env = .ok (.Ok (⟨.Active idx offset, init⟩, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  obtain ⟨flags, explicit, flagBytes, memory, encodedOffset, encodedInit, hf, hm, ho, hi, rfl⟩ := data_active_parts he
  obtain ⟨afterOffset, hbefore, hinit⟩ := hs.split
  obtain ⟨afterMemory, hmemory, hoffset⟩ := hbefore.split
  have hvec : At ByteVecEncoding data afterOffset init.val next := ⟨encodedInit, hi, hinit⟩
  obtain ⟨count, content, hn, hcount, encoded, hrep, hbytes⟩ := hvec.vector_split
  have hpayload : Wasm1.BytesAt data content init.val next := by simpa only [hrep.bytes] using hbytes
  obtain ⟨first, hflags, hindex⟩ := hmemory.split
  have hrf := hflags.read_u32 flags hf
  have hrm := metadata.decode_segment_index.profile_complete
    (show At (fun pair => SegmentIndexEncoding flags pair.1 pair.2)
      data first (idx, explicit) afterMemory from ⟨memory, hm, hindex⟩)
  have hro := metadata.decode_const_expr.complete (env := env) ⟨encodedOffset, ho, hoffset⟩ hv.2

  have hrc := reader.read_u32_leb.complete data afterOffset count content hcount
  have hx : metadata.decode_data_segment data pos env ⦃ r =>
      r = .Ok (⟨.Active idx offset, init⟩, next) ⦄ := by
    have hpass : flags ≠ 1#u32 := by
      rcases hm with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;> decide
    simp [metadata.decode_data_segment, hrf, hrm, core.result.Result.Insts.CoreOpsTry.branch]
    split <;> try contradiction
    step
    have hguard : ¬env.mem_types.val.length ≤ i.val := by have := hv.1; scalar_tac
    simp [hguard, hro, hrc]
    step
    have havail : content.val + n.val ≤ data.length := by
      have := hpayload.length
      have := hpayload.bound
      scalar_tac
    rw [metadata.have_bytes.complete data content n havail]
    simp only [bind_ok]
    step
    have hend : i2 = next := UScalar.eq_of_val_eq (by have := hpayload.length; scalar_tac)
    rw [hend, metadata.copy_bytes.complete data content next init hpayload]
    simp
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
  exact hr

private theorem data_passive_complete {data : Slice U8} {pos next : Usize}
    {env : metadata.Env} (init : alloc.vec.Vec U8)
    (hb : At (DataEncodingFor) data pos ⟨.Passive, init.val⟩ next) :
    metadata.decode_data_segment data pos env = .ok (.Ok (⟨.Passive, init⟩, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  cases he with
  | passive hf hi =>
    obtain ⟨first, hflags, hinit⟩ := hs.split
    have hvec : At ByteVecEncoding data first init.val next := ⟨_, hi, hinit⟩
    obtain ⟨count, content, hn, hcount, encoded, hrep, hbytes⟩ := hvec.vector_split
    have hpayload : Wasm1.BytesAt data content init.val next := by simpa only [hrep.bytes] using hbytes
    have hrf := hflags.read_u32 1#u32 hf
    have hrc := reader.read_u32_leb.complete data first count content hcount
    have hx : metadata.decode_data_segment data pos env ⦃ r =>
        r = .Ok (⟨.Passive, init⟩, next) ⦄ := by
      simp [metadata.decode_data_segment, hrf, hrc, core.result.Result.Insts.CoreOpsTry.branch]
      step
      have havail : content.val + n.val ≤ data.length := by
        have := hpayload.length
        have := hpayload.bound
        scalar_tac
      rw [metadata.have_bytes.complete data content n havail]
      simp only [bind_ok]
      step
      have hend : i = next := UScalar.eq_of_val_eq (by have := hpayload.length; scalar_tac)
      rw [hend, metadata.copy_bytes.complete data content next init hpayload]
      simp
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
    exact hr

/-- `metadata.decode_data_segment` accepts a `DataEncodingFor` span of a valid segment. -/
theorem metadata.decode_data_segment.profile_complete {data : Slice U8} {pos next : Usize}
    {env : metadata.Env} (segment : metadata.Data)
    (hb : At (DataEncodingFor) data pos (ModuleData.raw segment) next)
    (hv : ModuleData.Valid env segment) :
    metadata.decode_data_segment data pos env = .ok (.Ok (segment, next)) := by
  obtain ⟨mode, init⟩ := segment
  cases mode with
  | Active idx offset => exact data_active_complete idx offset init hb hv
  | Passive =>
    exact data_passive_complete init hb
/-- The data loop accepts the remaining valid segments of a repetition span and appends them to
`out`. -/
theorem metadata.decode_data_section_loop.profile_complete (data : Slice U8) (env : metadata.Env)
    (count : U32) (out : alloc.vec.Vec metadata.Data) (pos : Usize) (i : U32)
    (segments : List metadata.Data) (next : Usize)
    (hb : At (Rep (DataEncodingFor)) data pos (segments.map ModuleData.raw) next)
    (hc : i.val + segments.length = count.val) (hlen : out.val.length ≤ i.val)
    (hv : ∀ s ∈ segments, ModuleData.Valid env s) :
    ∃ result, metadata.decode_data_section_loop data env count out pos i = .ok (.Ok (result, next)) ∧
      result.val = out.val ++ segments := by
  induction segments generalizing out pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨out, ?_, by simp⟩
    unfold metadata.decode_data_section_loop
    rw [loop]
    simp [metadata.decode_data_section_loop.body, hstop, he]
  | cons segment segments ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := metadata.decode_data_segment.profile_complete segment hfirst (hv segment (by simp))
    obtain ⟨updated, hpush, hupdated⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out segment (by simp only [List.length_cons] at hc; scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by simp only [List.length_cons] at hc; scalar_tac))
    obtain ⟨result, hloop, hresult⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by simp only [hupdated, List.length_append, List.length_singleton]; scalar_tac)
      (by intro s hs; exact hv s (by simp [hs]))
    refine ⟨result, ?_, by simpa [hupdated, List.append_assoc] using hresult⟩
    unfold metadata.decode_data_section_loop
    rw [loop]
    simp [metadata.decode_data_section_loop.body, hmore, hread, hpush, hj,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact hloop

/-- `metadata.decode_data_section` accepts a vector span of valid segments. -/
theorem metadata.decode_data_section.profile_complete (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (segments : alloc.vec.Vec metadata.Data) (next : Usize)
    (hb : At (VecEncoding (DataEncodingFor)) data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s) :
    metadata.decode_data_section data pos env = .ok (.Ok (segments, next)) := by
  obtain ⟨count, first, hn, hc, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, he⟩ := metadata.decode_data_section_loop.profile_complete
    data env count (alloc.vec.Vec.new _) first 0#u32 segments.val next hentries
    (by simpa using hn.symm) (by simp) hv
  have heq : result = segments := alloc.vec.Vec.ext _ _ (by simpa using he)
  simp [metadata.decode_data_section, reader.read_u32_leb.complete data pos count first hc,
    hr, heq, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## TailComplete -/

section

/-!
# Completeness of the tail parser

`metadata.validate_tail.complete`: an independently encoded tail running to EOF, with valid
segments that agree with the data count, is accepted and returns those segments. The loop
lemmas show that the empty-visitor tail loop accepts custom sections and a data section.
Soundness is in `Module/Sections/Tail`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

open ModuleBinary

/-- `metadata.decode_custom_section` accepts a `CustomEncoding` span after its header. -/
theorem custom_decode {data : Slice U8} {pos next : Usize} {bytes : List U8}
    (he : CustomEncoding bytes) (hs : Wasm1.BytesAt data pos bytes next) :
    ∃ first custom, SectionHeader data pos 0#u8 first next ∧
      metadata.decode_custom_section data first next = .ok (.Ok custom) := by
  obtain ⟨nm, payload, nameBytes, hn, hsec⟩ := he
  obtain ⟨first, hh, _, rfl, hbody⟩ :=
    (show At (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = nameBytes ++ payload))
      data pos () next from ⟨bytes, hsec, hs⟩).section_split
  obtain ⟨content, hname, hpayload⟩ := hbody.split
  obtain ⟨custom, hc, _⟩ := metadata.decode_custom_section.complete_raw
    data first content next nm ⟨nameBytes, hn, hname⟩ (by have := hpayload.length; omega)
  exact ⟨first, custom, hh, hc⟩

/-- The tail loop at EOF returns the accumulated segments. -/
theorem loop_eof (data : Slice U8) (env : metadata.Env) (segments : alloc.vec.Vec metadata.Data) (seen : Bool)

    (hcount : ∀ count, env.data_count = some count → count.val = segments.val.length) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () segments (Slice.len data) seen = .ok (.Ok ⟨segments⟩, ()) := by
  have hb : metadata.validate_tail_with_loop.body metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () segments (Slice.len data) seen ⦃ r =>
      r = .done ((.Ok ⟨segments⟩), ()) ⦄ := by
    unfold metadata.validate_tail_with_loop.body
    simp only [ge_iff_le, le_refl, ↓reduceIte]
    cases hc : env.data_count with
    | none => simp
    | some count =>
      step
      have hlen : r.val = segments.val.length := by have := hcount count hc; scalar_tac
      simp [hlen]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hb
  unfold metadata.validate_tail_with_loop
  rw [loop]
  simp [hr]

/-- Leading custom sections do not change the loop result. -/
theorem customs_prefix {data : Slice U8} {env : metadata.Env} {segments : alloc.vec.Vec metadata.Data}
    {pos next : Usize} {seen : Bool} {bytes : List U8}
    (he : CustomsEncoding bytes) (hb : Wasm1.BytesAt data pos bytes next)
    {result : core.result.Result metadata.Tail error.Error × Unit}
    (hnext : metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () segments next seen = .ok result) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () segments pos seen = .ok result := by
  induction he generalizing pos with
  | nil => simpa [hb.empty] using hnext
  | cons hfirst hrest ih =>
    obtain ⟨middle, hf, ht⟩ := hb.split
    obtain ⟨first, custom, hh, hc⟩ := custom_decode hfirst hf
    have hmore : ¬pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hr := metadata.read_section_header.complete data pos 0#u8 first middle hh
    have hs := ih ht
    unfold metadata.validate_tail_with_loop
    rw [loop]
    simp [metadata.validate_tail_with_loop.body, hmore, hr, hc, metadata.SECTION_CUSTOM,
      metadata.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch]
    simpa [metadata.validate_tail_with_loop, metadata.validate_tail_with_loop.body, metadata.SECTION_CUSTOM,
      metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor,
      metadata.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch] using hs

/-- A leading data section of valid segments does not change the loop result. -/
theorem data_prefix {data : Slice U8} {env : metadata.Env} {segments : alloc.vec.Vec metadata.Data}
    {pos next : Usize} (hbytes : At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor)))
      data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s)
    {result : core.result.Result metadata.Tail error.Error × Unit}
    (hnext : metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () segments next true = .ok result) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () (alloc.vec.Vec.new _) pos false = .ok result := by
  obtain ⟨first, hh, hp⟩ := hbytes.section_split
  have hr := metadata.read_section_header.complete data pos 11#u8 first next hh
  have hd := metadata.decode_data_section.profile_complete data first env segments next hp hv
  have hmore : ¬pos ≥ Slice.len data := by have := hh.span; scalar_tac
  unfold metadata.validate_tail_with_loop
  rw [loop]
  simp [metadata.validate_tail_with_loop.body, hmore, hr, hd, metadata.SECTION_CUSTOM,
    metadata.SECTION_DATA, core.result.Result.Insts.CoreOpsTry.branch]
  simpa [metadata.validate_tail_with_loop, metadata.validate_tail_with_loop.body,
    metadata.SECTION_CUSTOM, metadata.SECTION_DATA,
    core.result.Result.Insts.CoreOpsTry.branch] using hnext

private theorem optional_cases {α : Type} {id R absent value bytes}
    (h : @OptionalSectionEncoding α id R absent value bytes) :
    (value = absent ∧ bytes = []) ∨ SectionEncoding id R value bytes := by
  cases h with
  | absent => exact .inl ⟨rfl, rfl⟩
  | present hs => exact .inr hs

/-- The tail loop accepts a tail encoding to EOF and returns its segments. -/
theorem loop_complete {data : Slice U8} {env : metadata.Env} {segments : alloc.vec.Vec metadata.Data}
    {pos : Usize} (hb : At (fun segments bytes => Encoding segments bytes) data pos (segments.val.map ModuleData.raw) (Slice.len data))
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s)
    (hcount : ∀ count, env.data_count = some count → count.val = segments.val.length) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env () (alloc.vec.Vec.new _) pos false = .ok (.Ok ⟨segments⟩, ()) := by
  obtain ⟨bytes, hencoding, hspan⟩ := hb
  obtain ⟨chunk, trailing, hchunkEncoding, htrailing, hbytesEq⟩ := hencoding
  obtain ⟨before, sectionBytes, hbefore, hsection, hchunkEq⟩ := hchunkEncoding
  rw [hbytesEq, hchunkEq] at hspan
  obtain ⟨afterSection, hchunk, htrail⟩ := hspan.split
  obtain ⟨sectionPos, hcustom, hsec⟩ := hchunk.split
  apply customs_prefix hbefore hcustom
  rcases optional_cases hsection with ⟨hnil, heBytes⟩ | hs
  · rw [heBytes] at hsec
    have he : segments = alloc.vec.Vec.new metadata.Data := by
      apply alloc.vec.Vec.ext
      simpa using (List.map_eq_nil_iff.mp (show segments.val.map ModuleData.raw = [] from hnil))
    subst segments
    have hpos := hsec.empty
    subst afterSection
    exact customs_prefix htrailing htrail (loop_eof data env (alloc.vec.Vec.new _) false hcount)
  · exact data_prefix ⟨sectionBytes, hs, hsec⟩ hv
      (customs_prefix htrailing htrail (loop_eof data env segments true hcount))

end Itasca.ModuleTail

namespace Itasca

/-- `metadata.validate_tail` accepts a tail encoding to EOF with valid, count-consistent segments
and returns them. -/
theorem metadata.validate_tail.complete {data : Slice U8} {pos : Usize} {env : metadata.Env}
    (tail : metadata.Tail)
    (hb : ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes) data pos
      (tail.data.val.map ModuleData.raw) (Slice.len data))
    (hv : ∀ s ∈ tail.data.val, ModuleData.Valid env s)
    (hcount : ∀ count, env.data_count = some count → count.val = tail.data.val.length) :
    metadata.validate_tail data pos env = .ok (.Ok tail) := by
  have h := ModuleTail.loop_complete hb hv hcount
  cases tail
  simp [metadata.validate_tail, metadata.validate_tail_with, h]

end Itasca

end
