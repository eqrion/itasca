import Itasca.Module.ModuleTail
import Itasca.Module.ModuleDataComplete
import Itasca.Module.ModuleNamesComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

open ModuleBinary

theorem custom_decode {data : Slice U8} {pos next : Usize} {bytes : List U8}
    (he : CustomEncoding bytes) (hs : Wasm.BytesAt data pos bytes next) :
    ∃ first custom, SectionHeader data pos 0#u8 first next ∧
      module.decode_custom_section data first next = .ok (.Ok custom) := by
  obtain ⟨nm, payload, nameBytes, hn, hsec⟩ := he
  obtain ⟨first, hh, _, rfl, hbody⟩ :=
    (show At (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = nameBytes ++ payload))
      data pos () next from ⟨bytes, hsec, hs⟩).section_split
  obtain ⟨content, hname, hpayload⟩ := hbody.split
  obtain ⟨custom, hc, _⟩ := module.decode_custom_section.complete_raw
    data first content next nm ⟨nameBytes, hn, hname⟩ (by have := hpayload.length; omega)
  exact ⟨first, custom, hh, hc⟩

theorem loop_eof (data : Slice U8) (env : module.Env) (segments : alloc.vec.Vec module.Data) (seen : Bool)
    (profile : ValidationProfile := .Wasm1) :
    module.validate_tail_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      data env profile () segments (Slice.len data) seen = .ok (.Ok ⟨segments⟩, ()) := by
  unfold module.validate_tail_with_loop
  rw [loop]
  simp [module.validate_tail_with_loop.body]

theorem customs_prefix {profile} {data : Slice U8} {env : module.Env} {segments : alloc.vec.Vec module.Data}
    {pos next : Usize} {seen : Bool} {bytes : List U8}
    (he : CustomsEncoding bytes) (hb : Wasm.BytesAt data pos bytes next)
    {result : core.result.Result module.Tail error.Error × Unit}
    (hnext : module.validate_tail_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      data env profile () segments next seen = .ok result) :
    module.validate_tail_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      data env profile () segments pos seen = .ok result := by
  induction he generalizing pos with
  | nil => simpa [hb.empty] using hnext
  | cons hfirst hrest ih =>
    obtain ⟨middle, hf, ht⟩ := hb.split
    obtain ⟨first, custom, hh, hc⟩ := custom_decode hfirst hf
    have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hr := module.read_section_header.complete data pos 0#u8 first middle hh
    have hs := ih ht
    unfold module.validate_tail_with_loop
    rw [loop]
    simp [module.validate_tail_with_loop.body, hmore, hr, hc, module.SECTION_CUSTOM,
      module.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch]
    simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body, module.SECTION_CUSTOM,
      module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor,
      module.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch] using hs

theorem data_prefix {profile} {data : Slice U8} {env : module.Env} {segments : alloc.vec.Vec module.Data}
    {pos next : Usize} (hbytes : At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor profile)))
      data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s)
    {result : core.result.Result module.Tail error.Error × Unit}
    (hnext : module.validate_tail_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      data env profile () segments next true = .ok result) :
    module.validate_tail_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      data env profile () (alloc.vec.Vec.new _) pos false = .ok result := by
  obtain ⟨first, hh, hp⟩ := hbytes.section_split
  have hr := module.read_section_header.complete data pos 11#u8 first next hh
  have hd := module.decode_data_section.profile_complete data first env profile segments next hp hv
  have hmore : ¬pos ≥ Slice.len data := by have := hh.span; scalar_tac
  unfold module.validate_tail_with_loop
  rw [loop]
  simp [module.validate_tail_with_loop.body, hmore, hr, hd, module.SECTION_CUSTOM,
    module.SECTION_DATA, core.result.Result.Insts.CoreOpsTry.branch]
  simpa [module.validate_tail_with_loop, module.validate_tail_with_loop.body,
    module.SECTION_CUSTOM, module.SECTION_DATA,
    core.result.Result.Insts.CoreOpsTry.branch] using hnext

private theorem optional_cases {α : Type} {id R absent value bytes}
    (h : @OptionalSectionEncoding α id R absent value bytes) :
    (value = absent ∧ bytes = []) ∨ SectionEncoding id R value bytes := by
  cases h with
  | absent => exact .inl ⟨rfl, rfl⟩
  | present hs => exact .inr hs

theorem loop_complete {profile} {data : Slice U8} {env : module.Env} {segments : alloc.vec.Vec module.Data}
    {pos : Usize} (hb : At (fun segments bytes => Encoding segments bytes profile) data pos (segments.val.map ModuleData.raw) (Slice.len data))
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s) :
    module.validate_tail_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
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
    have he : segments = alloc.vec.Vec.new module.Data := by
      apply alloc.vec.Vec.ext
      simpa using (List.map_eq_nil_iff.mp (show segments.val.map ModuleData.raw = [] from hnil))
    subst segments
    have hpos := hsec.empty
    subst afterSection
    exact customs_prefix htrailing htrail (loop_eof data env (alloc.vec.Vec.new _) false profile)
  · exact data_prefix ⟨sectionBytes, hs, hsec⟩ hv
      (customs_prefix htrailing htrail (loop_eof data env segments true profile))

end Itasca.ModuleTail

namespace Itasca

/-- Complete decoding of the independent data/custom-section suffix. -/
theorem module.validate_tail.complete {profile} {data : Slice U8} {pos : Usize} {env : module.Env}
    (tail : module.Tail)
    (hb : ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes profile) data pos
      (tail.data.val.map ModuleData.raw) (Slice.len data))
    (hv : ∀ s ∈ tail.data.val, ModuleData.Valid env s) :
    module.validate_tail data pos env profile = .ok (.Ok tail) := by
  have h := ModuleTail.loop_complete hb hv
  cases tail
  simp [module.validate_tail, module.validate_tail_with, h]

end Itasca
