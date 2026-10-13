import Itasca.Module.Readers.BasicComplete
import Itasca.Module.Readers.Header

/-!
# Completeness of section framing

Acceptance (`.complete`) of `module.have_bytes`, `module.copy_bytes`, `module.read_section_header`
and `module.read_header` from independent byte spans, and `At.section_split`, which recovers the
header and payload spans of a complete section encoding. Soundness is in `Module/Readers/Basic` and
`Module/Readers/Header`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A section encoding splits into a `SectionHeader` and the payload span. -/
theorem At.section_split {α : Type} {R : α → List U8 → Prop}
    {data pos next id value} (h : At (SectionEncoding id R) data pos value next) :
    ∃ first, SectionHeader data pos id first next ∧ At R data first value next := by
  obtain ⟨bytes, ⟨sizeBytes, payload, hsize, hvalue, rfl⟩, hs⟩ := h
  obtain ⟨middle, hid, hrest⟩ :=
    (show Wasm1.BytesAt data pos ([id] ++ (sizeBytes ++ payload)) next from hs).split
  obtain ⟨first, hcount, hbytes⟩ := hrest.split
  let count : U32 := U32.ofNatCore payload.length (by have := hsize.value_lt; scalar_tac)
  have hc : count.val = payload.length := by simp [count]
  exact ⟨first, ⟨middle, count, ⟨[id], rfl, hid⟩,
    hcount.u32_decoded count (by simpa [hc] using hsize),
    by simpa [hc] using hbytes.length, hbytes.bound⟩, ⟨payload, hvalue, hbytes⟩⟩

end Itasca.ModuleBinary

namespace Itasca
open ModuleBinary

/-- `module.have_bytes` accepts when the bytes are available. -/
theorem module.have_bytes.complete (data : Slice U8) (pos n : Usize)
    (h : pos.val + n.val ≤ data.length) : module.have_bytes data pos n = .ok (.Ok ()) := by
  obtain ⟨r, hr, hgood, _⟩ := WP.spec_imp_exists
    (module.have_bytes.spec data pos n (by omega))
  exact (hgood.mpr h) ▸ hr

/-- Copying a known byte interval recovers its exact vector, including empty intervals. -/
theorem module.copy_bytes.complete (data : Slice U8) (first last : Usize)
    (out : alloc.vec.Vec U8) (h : Wasm1.BytesAt data first out.val last) :
    module.copy_bytes data first last = .ok out := by
  obtain ⟨result, hr, hs⟩ := WP.spec_imp_exists
    (module.copy_bytes.spec data first last (by have := h.length; omega) h.bound)
  have he : result = out := alloc.vec.Vec.ext _ _
    (List.append_cancel_right (hs.suffix.symm.trans h.suffix))
  simpa [he] using hr

/-- `module.read_section_header` accepts a `SectionHeader` span and returns its id and bounds. -/
theorem module.read_section_header.complete (data : Slice U8) (pos : Usize)
    (id : U8) (first last : Usize) (h : SectionHeader data pos id first last) :
    module.read_section_header data pos = .ok (.Ok (id, first, last)) := by
  obtain ⟨middle, count, hid, hc, hlast, hbound⟩ := h
  have hr := hid.read_byte
  have hcount := reader.read_u32_leb.complete data middle count first hc
  have hs : module.read_section_header data pos ⦃ r => r = .Ok (id, first, last) ⦄ := by
    simp [module.read_section_header, hr, hcount, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hb : first.val + n.val ≤ data.length := by scalar_tac
    rw [module.have_bytes.complete data first n hb]
    simp only [bind_ok]
    step*
    congr 3
    apply UScalar.eq_of_val_eq
    scalar_tac
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

private theorem read_at (data : Slice U8) (pos next : Usize) (byte : U8)
    (hp : pos.val < data.length) (hn : next.val = pos.val + 1)
    (hb : data.val[pos.val] = byte) :
    reader.read_byte data pos = .ok (.Ok (byte, next)) := by
  obtain ⟨_, hr, p, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
  have he : p = next := UScalar.eq_of_val_eq (hnext.trans hn.symm)
  simpa [he, hb] using hr

/-- `module.read_header` accepts the magic and version bytes. -/
theorem module.read_header.complete (data : Slice U8) (next : Usize)
    (h : Wasm1.BytesAt data 0#usize magicVersion next) :
    module.read_header data = .ok (.Ok next) := by
  have hn : next = 8#usize := UScalar.eq_of_val_eq (by simpa [magicVersion] using h.length)
  subst next
  have hdata : data.val = magicVersion ++ data.val.drop 8 := by simpa using h.suffix
  generalize hrest : data.val.drop 8 = rest at hdata
  have h0 := read_at data 0#usize 1#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h4 := read_at data 4#usize 5#usize 1#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h5 := read_at data 5#usize 6#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h6 := read_at data 6#usize 7#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  have h7 := read_at data 7#usize 8#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion])
  simp [module.read_header, h0, h1, h2, h3, h4, h5, h6, h7,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
