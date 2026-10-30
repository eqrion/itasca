import Itasca.Module.Sections.Tail
import Itasca.Module.Sections.DataComplete
import Itasca.Module.Readers.NamesComplete

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
    (profile : ValidationProfile := .Wasm1)
    (hcount : ∀ count, env.data_count = some count → count.val = segments.val.length) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () segments (Slice.len data) seen = .ok (.Ok ⟨segments⟩, ()) := by
  have hb : metadata.validate_tail_with_loop.body metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () segments (Slice.len data) seen ⦃ r =>
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
theorem customs_prefix {profile} {data : Slice U8} {env : metadata.Env} {segments : alloc.vec.Vec metadata.Data}
    {pos next : Usize} {seen : Bool} {bytes : List U8}
    (he : CustomsEncoding bytes) (hb : Wasm1.BytesAt data pos bytes next)
    {result : core.result.Result metadata.Tail error.Error × Unit}
    (hnext : metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () segments next seen = .ok result) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () segments pos seen = .ok result := by
  induction he generalizing pos with
  | nil => simpa [hb.empty] using hnext
  | cons hfirst hrest ih =>
    obtain ⟨middle, hf, ht⟩ := hb.split
    obtain ⟨first, custom, hh, hc⟩ := custom_decode hfirst hf
    have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
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
theorem data_prefix {profile} {data : Slice U8} {env : metadata.Env} {segments : alloc.vec.Vec metadata.Data}
    {pos next : Usize} (hbytes : At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor profile)))
      data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s)
    {result : core.result.Result metadata.Tail error.Error × Unit}
    (hnext : metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () segments next true = .ok result) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () (alloc.vec.Vec.new _) pos false = .ok result := by
  obtain ⟨first, hh, hp⟩ := hbytes.section_split
  have hr := metadata.read_section_header.complete data pos 11#u8 first next hh
  have hd := metadata.decode_data_section.profile_complete data first env profile segments next hp hv
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
theorem loop_complete {profile} {data : Slice U8} {env : metadata.Env} {segments : alloc.vec.Vec metadata.Data}
    {pos : Usize} (hb : At (fun segments bytes => Encoding segments bytes profile) data pos (segments.val.map ModuleData.raw) (Slice.len data))
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s)
    (hcount : ∀ count, env.data_count = some count → count.val = segments.val.length) :
    metadata.validate_tail_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
      data env profile () (alloc.vec.Vec.new _) pos false = .ok (.Ok ⟨segments⟩, ()) := by
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
    exact customs_prefix htrailing htrail (loop_eof data env (alloc.vec.Vec.new _) false profile hcount)
  · exact data_prefix ⟨sectionBytes, hs, hsec⟩ hv
      (customs_prefix htrailing htrail (loop_eof data env segments true profile hcount))

end Itasca.ModuleTail

namespace Itasca

/-- `metadata.validate_tail` accepts a tail encoding to EOF with valid, count-consistent segments
and returns them. -/
theorem metadata.validate_tail.complete {profile} {data : Slice U8} {pos : Usize} {env : metadata.Env}
    (tail : metadata.Tail)
    (hb : ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes profile) data pos
      (tail.data.val.map ModuleData.raw) (Slice.len data))
    (hv : ∀ s ∈ tail.data.val, ModuleData.Valid env s)
    (hcount : ∀ count, env.data_count = some count → count.val = tail.data.val.length) :
    metadata.validate_tail data pos env profile = .ok (.Ok tail) := by
  have h := ModuleTail.loop_complete hb hv hcount
  cases tail
  simp [metadata.validate_tail, metadata.validate_tail_with, h]

end Itasca
