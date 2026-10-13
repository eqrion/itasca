import Itasca.Module.Readers.Utf8Complete
import Itasca.Module.Readers.Names

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- Name framing and byte copying preserve the UTF-8 scanner's exact reply. -/
theorem module.decode_name.from_utf8 (data : Slice U8) (pos : Usize)
    (nm : alloc.vec.Vec U8) (next : Usize)
    (h : At ByteVecEncoding data pos nm.val next)
    (reply : core.result.Result Unit error.Error)
    (hutf8 : module.validate_utf8 (alloc.vec.Vec.deref nm) = .ok reply) :
    module.decode_name data pos = .ok (match reply with
      | .Ok _ => .Ok (nm, next)
      | .Err e => .Err e) := by
  obtain ⟨count, middle, hcount, hlen, encoded, hrep, hbytes⟩ := h.vector_split
  have hb : Wasm1.BytesAt data middle nm.val next := by simpa only [hrep.bytes] using hbytes
  have hr := reader.read_u32_leb.complete data pos count middle hlen
  have hs : module.decode_name data pos ⦃ r => r = (match reply with
      | .Ok _ => .Ok (nm, next)
      | .Err e => .Err e) ⦄ := by
    simp [module.decode_name, hr, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hroom : middle.val + n.val ≤ data.length := by have := hb.length; have := hb.bound; scalar_tac
    rw [module.have_bytes.complete data middle n hroom]
    simp only [bind_ok]
    step
    have hend : i = next := UScalar.eq_of_val_eq (by have := hb.length; scalar_tac)
    rw [hend, module.copy_bytes.complete data middle next nm hb]
    simp only [bind_ok, hutf8]
    cases reply <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr


/-- Independent name encoding suffices for the exact parser result. -/
theorem module.decode_name.complete (data : Slice U8) (pos : Usize)
    (nm : alloc.vec.Vec U8) (next : Usize) (h : At NameEncoding data pos nm.val next) :
    module.decode_name data pos = .ok (.Ok (nm, next)) := by
  obtain ⟨bytes, ⟨hvec, hutf8⟩, hs⟩ := h
  exact module.decode_name.from_utf8 data pos nm next ⟨bytes, hvec, hs⟩ (.Ok ())
    (module.validate_utf8.complete _ (by simpa [alloc.vec.Vec.deref] using hutf8))

theorem module.decode_name.complete_raw (data : Slice U8) (pos : Usize)
    (nm : List U8) (next : Usize) (h : At NameEncoding data pos nm next) :
    ∃ value, module.decode_name data pos = .ok (.Ok (value, next)) ∧ value.val = nm := by
  have hsize : nm.length ≤ Usize.max := by
    obtain ⟨bytes, ⟨hvec, _⟩, _⟩ := h
    obtain ⟨count, _, hc, _, _⟩ := hvec
    have := hc.value_lt
    scalar_tac
  let value := alloc.vec.Vec.from nm hsize
  exact ⟨value, module.decode_name.complete data pos value next (by simpa [value] using h), by simp [value]⟩

theorem module.decode_custom_section.complete (data : Slice U8) (pos next last : Usize)
    (nm : alloc.vec.Vec U8) (h : At NameEncoding data pos nm.val next)
    (hbefore : next.val ≤ last.val) :
    module.decode_custom_section data pos last = .ok (.Ok
      ⟨alloc.vec.Vec.len nm, next, last⟩) := by
  have hread := module.decode_name.complete data pos nm next h
  simp [module.decode_custom_section, hread, hbefore, core.result.Result.Insts.CoreOpsTry.branch]


theorem module.decode_custom_section.complete_raw (data : Slice U8) (pos next last : Usize)
    (nm : List U8) (h : At NameEncoding data pos nm next) (hbefore : next.val ≤ last.val) :
    ∃ custom, module.decode_custom_section data pos last = .ok (.Ok custom) ∧
      custom.name_len.val = nm.length ∧ custom.payload_start = next ∧ custom.payload_end = last := by
  obtain ⟨value, hr, hv⟩ := module.decode_name.complete_raw data pos nm next h
  refine ⟨⟨alloc.vec.Vec.len value, next, last⟩, ?_, by simpa using congrArg List.length hv, rfl, rfl⟩
  simp [module.decode_custom_section, hr, hbefore, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
