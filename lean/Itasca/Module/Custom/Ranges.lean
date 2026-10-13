import Itasca.Module.Custom.TraceDefs

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- The public `name_len` field identifies exactly the UTF-8 bytes immediately
before `payload_start`, as documented by the Rust CustomSection API. -/
theorem CustomAt.name_bytes {data start finish chunk} (h : CustomAt data start finish chunk) :
    ∃ nameStart nm, Wasm.BytesAt data nameStart nm chunk.payload_start ∧ ModuleBinary.Utf8 nm ∧
      nameStart.val + chunk.name_len.val = chunk.payload_start.val ∧ start.val < nameStart.val := by
  obtain ⟨first, nm, hh, hnameAt, hp, he, hlen⟩ := h
  obtain ⟨bytes, hn, hb⟩ := hnameAt
  obtain ⟨count, hc, hbytes⟩ := ModuleBinary.ByteVecEncoding.iff.mp hn.1
  rw [hbytes] at hb
  obtain ⟨nameStart, hcount, hname⟩ := hb.split
  refine ⟨nameStart, nm, hname, hn.2, ?_, ?_⟩
  · have := hname.length
    omega
  · have := hh.span
    have := hcount.length
    omega

/-- Both metadata intervals lie within the original module buffer; computing
the name start by subtraction cannot underflow. -/
theorem CustomAt.bounds {data start finish chunk} (h : CustomAt data start finish chunk) :
    chunk.name_len.val ≤ chunk.payload_start.val ∧
      chunk.payload_start.val ≤ chunk.payload_end.val ∧ chunk.payload_end.val ≤ data.length := by
  obtain ⟨nameStart, nm, hn, hu, he, hs⟩ := h.name_bytes
  obtain ⟨first, _, hh, _, hp, hend, _⟩ := h
  have := hh.span
  subst finish
  omega

end Itasca.ModuleTrace
