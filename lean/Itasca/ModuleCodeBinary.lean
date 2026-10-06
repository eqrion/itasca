import Itasca.ModuleLocals

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The body's streaming provenance concatenates to the module grammar's
independent repetition relation. -/
theorem consumed_rep {data start tokens next}
    (h : Wasm.Consumed data start tokens next) :
    At (Rep Wasm.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Wasm.BytesAt.nil _ _ hb⟩
  | snoc hprev ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

theorem bodyEncoding_of_body {data ops} (h : Wasm.BodyEncoding data ops) :
    BodyEncoding ops data.val := by
  obtain ⟨tokens, next, hs, hn, ht⟩ := h
  obtain ⟨bytes, he, hb⟩ := consumed_rep hs
  have heq : data.val = bytes := by simpa [hn] using hb.suffix
  exact ⟨tokens, heq.symm ▸ he, ht⟩

/-- A successful slice operation preserves the precise parent-buffer interval. -/
theorem slice_bytes {data : Slice U8} {first last : Usize} {body : Slice U8}
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length)
    (hbody : body.val = data.val.slice first.val last.val) :
    Wasm.BytesAt data first body.val last := by
  refine ⟨?_, ?_, hlast⟩
  · rw [hbody, List.slice]
    have he : first.val + (last.val - first.val) = last.val := by omega
    simpa only [List.drop_drop, he] using
      (List.take_append_drop (last.val - first.val) (data.val.drop first.val)).symm
  · rw [hbody, List.slice_length]
    simp only [Slice.length] at hlast
    omega

/-- Combine the declared size, grouped locals, and complete body bytes into
one code-entry encoding of exactly the interval returned by the parser. -/
theorem codeEncoding_of_parts {data start content localEnd last size groups body ops}
    (hsize : Leb128.Decoded data start size content)
    (hlength : last.val = content.val + size.val)
    (hlocals : At (VecEncoding LocalEncoding) data content groups localEnd)
    (hbodybytes : Wasm.BytesAt data localEnd body.val last)
    (hbody : Wasm.BodyEncoding body ops) :
    At CodeEncoding data start ⟨groups, ops⟩ last := by
  obtain ⟨header, hh, hn, hb, he⟩ := hsize
  obtain ⟨localBytes, hl, hls⟩ := hlocals
  have hlen : size.val = localBytes.length + body.val.length := by
    have := hls.length
    have := hbodybytes.length
    omega
  refine ⟨header ++ localBytes ++ body.val,
    ⟨header, localBytes, body.val, ?_, hl, bodyEncoding_of_body hbody, rfl⟩, ?_⟩
  · simpa [hlen] using he
  · exact ((⟨hh, hn, hb⟩ : Wasm.BytesAt data start header content).append hls).append hbodybytes

end Itasca.ModuleBinary
