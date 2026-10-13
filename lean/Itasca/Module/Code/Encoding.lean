import Itasca.Module.Code.Locals

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The body's streaming provenance concatenates to the module grammar's
independent repetition relation. -/
theorem consumed_rep {data start tokens next}
    (h : Wasm1.Consumed data start tokens next) :
    At (Rep Wasm1.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Wasm1.BytesAt.nil _ _ hb⟩
  | snoc hprev ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

theorem bodyEncoding_of_body {data ops} (h : Wasm1.BodyEncoding data ops) :
    BodyEncoding ops data.val := by
  obtain ⟨tokens, next, hs, hn, ht⟩ := h
  obtain ⟨bytes, he, hb⟩ := consumed_rep hs
  have heq : data.val = bytes := by simpa [hn] using hb.suffix
  exact ⟨tokens, heq.symm ▸ he, ht⟩

/-- A successful slice operation preserves the precise parent-buffer interval. -/
theorem slice_bytes {data : Slice U8} {first last : Usize} {body : Slice U8}
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length)
    (hbody : body.val = data.val.slice first.val last.val) :
    Wasm1.BytesAt data first body.val last := by
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
    (hbodybytes : Wasm1.BytesAt data localEnd body.val last)
    (hbody : Wasm1.BodyEncoding body ops) :
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
  · exact ((⟨hh, hn, hb⟩ : Wasm1.BytesAt data start header content).append hls).append hbodybytes


theorem rep_consumed {data start next tokens bytes}
    (he : Rep Wasm1.TokenEncoding tokens bytes) (hs : Wasm1.BytesAt data start bytes next) :
    Wasm1.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht hrest ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Wasm1.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

theorem body_of_bodyEncoding {data : Slice U8} {ops}
    (he : BodyEncoding ops data.val) : Wasm1.BodyEncoding data ops := by
  obtain ⟨tokens, ht, hb⟩ := he
  refine ⟨tokens, Slice.len data, rep_consumed ht ?_, rfl, hb⟩
  exact ⟨by simp, by simp, by simp⟩

end Itasca.ModuleBinary
