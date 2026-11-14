import Itasca.Module.Readers.Types
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Support.Result

/-!
Sections, each formerly its own module: BasicComplete, Header, FramingComplete, Copies, SegmentIndex, Utf8.
-/

/-! ## BasicComplete -/

section

/-!
# Completeness of the primitive readers

Inversion lemmas for `At` over index, byte, repetition and vector encodings, and acceptance
(`.complete`) of `metadata.decode_value_type` and `metadata.decode_elem_type` from independent
encodings. The matching soundness specs are in `Module/Readers/Basic`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- An `IndexEncoding` span is a decoded `u32`. -/
theorem At.index_decoded {data pos idx next} (h : At IndexEncoding data pos idx next) :
    Leb128.Decoded data pos idx next := by
  obtain ⟨bytes, he, hs⟩ := h
  exact hs.u32_decoded idx he

/-- `reader.read_u32_leb` reads an `IndexEncoding` span. -/
theorem At.read_index {data pos idx next} (h : At IndexEncoding data pos idx next) :
    reader.read_u32_leb data pos = .ok (.Ok (idx, next)) :=
  reader.read_u32_leb.complete data pos idx next h.index_decoded

/-- `reader.read_byte` reads a `ByteEncoding` span. -/
theorem At.read_byte {data pos byte next} (h : At ByteEncoding data pos byte next) :
    reader.read_byte data pos = .ok (.Ok (byte, next)) := h.byte.read_byte

/-- An empty repetition consumes nothing. -/
theorem At.rep_nil {α : Type} {R : α → List U8 → Prop} {data pos next}
    (h : At (Rep R) data pos [] next) : next = pos := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he
  exact hs.empty

/-- A nonempty repetition splits into its first element and the rest. -/
theorem At.rep_cons {α : Type} {R : α → List U8 → Prop} {data pos value values next}
    (h : At (Rep R) data pos (value :: values) next) :
    ∃ middle, At R data pos value middle ∧ At (Rep R) data middle values next := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he with
  | cons hfirst hrest =>
      obtain ⟨middle, hf, ht⟩ := hs.split
      exact ⟨middle, ⟨_, hfirst, hf⟩, ⟨_, hrest, ht⟩⟩

/-- A vector encoding splits into a decoded `u32` count equal to the length and the repeated
elements. The count's LEB encoding fits in a `u32`, and nonminimal encodings are admitted. -/
theorem At.vector_split {α : Type} {R : α → List U8 → Prop} {data pos values next}
    (h : At (VecEncoding R) data pos values next) :
    ∃ count middle, count.val = values.length ∧ Leb128.Decoded data pos count middle ∧
      At (Rep R) data middle values next := by
  obtain ⟨bytes, ⟨countBytes, entries, hc, he, rfl⟩, hs⟩ := h
  let count : U32 := U32.ofNatCore values.length (by have := hc.value_lt; scalar_tac)
  have hcount : count.val = values.length := by simp [count]
  obtain ⟨middle, hf, ht⟩ := hs.split
  exact ⟨count, middle, hcount, hf.u32_decoded count (by simpa [hcount] using hc), ⟨entries, he, ht⟩⟩

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary

/-- `metadata.decode_value_type` accepts an independently encoded value type. -/
theorem metadata.decode_value_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.ValueType) (next : Usize) (h : At ValueTypeEncoding data pos ty next) :
    metadata.decode_value_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases ty <;>
    simp_all [metadata.decode_value_type, valueByte,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_elem_type` accepts an independently encoded element type. -/
theorem metadata.decode_elem_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.ElemType) (next : Usize) (h : At ElemTypeEncoding data pos ty next) :
    metadata.decode_elem_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases ty <;>
    simp_all [metadata.decode_elem_type, elemByte,
      core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## Header -/

section

/-!
# Module header reader

`metadata.read_header.spec`: an accepted header is the magic and version bytes at offset 0. The
completeness counterpart is in `Module/Readers/FramingComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- An accepted result of `metadata.read_header` consumes exactly the magic and version bytes. -/
theorem metadata.read_header.spec (data : Slice U8) :
    metadata.read_header data ⦃ r => match r with
      | .Ok next => Wasm1.BytesAt data 0#usize magicVersion next
      | .Err _ => True ⦄ := by
  obtain ⟨r, h1, hb1⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data 0#usize)
  cases r with
  | Err e =>
      simp [metadata.read_header, h1, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨b1, p1⟩ := pair
      obtain ⟨r, h2, hb2⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p1)
      cases r with
      | Err e =>
          simp [metadata.read_header, h1, h2, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨b2, p2⟩ := pair
          obtain ⟨r, h3, hb3⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p2)
          cases r with
          | Err e =>
              simp [metadata.read_header, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
              obtain ⟨b3, p3⟩ := pair
              obtain ⟨r, h4, hb4⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p3)
              cases r with
              | Err e =>
                  simp [metadata.read_header, h1, h2, h3, h4, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                  obtain ⟨b4, p4⟩ := pair
                  obtain ⟨r, h5, hb5⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p4)
                  cases r with
                  | Err e =>
                      simp [metadata.read_header, h1, h2, h3, h4, h5, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                        error.Error.Insts.CoreConvertFromOpError.from]
                      all_goals split_ifs <;> simp
                  | Ok pair =>
                      obtain ⟨b5, p5⟩ := pair
                      obtain ⟨r, h6, hb6⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p5)
                      cases r with
                      | Err e =>
                          simp [metadata.read_header, h1, h2, h3, h4, h5, h6, core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                            error.Error.Insts.CoreConvertFromOpError.from]
                          all_goals split_ifs <;> simp
                      | Ok pair =>
                          obtain ⟨b6, p6⟩ := pair
                          obtain ⟨r, h7, hb7⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p6)
                          cases r with
                          | Err e =>
                              simp [metadata.read_header, h1, h2, h3, h4, h5, h6, h7, core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                error.Error.Insts.CoreConvertFromOpError.from]
                              all_goals split_ifs <;> simp
                          | Ok pair =>
                              obtain ⟨b7, p7⟩ := pair
                              obtain ⟨r, h8, hb8⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p7)
                              cases r with
                              | Err e =>
                                  simp [metadata.read_header, h1, h2, h3, h4, h5, h6, h7, h8, core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                                    error.Error.Insts.CoreConvertFromOpError.from]
                                  all_goals split_ifs <;> simp
                              | Ok pair =>
                                  obtain ⟨b8, p8⟩ := pair
                                  simp [metadata.read_header, h1, h2, h3, h4, h5, h6, h7, h8,
                                    core.result.Result.Insts.CoreOpsTry.branch]
                                  split_ifs <;> simp_all
                                  have hbytes := ((((((((At.byte hb1).append (At.byte hb2)).append (At.byte hb3)).append (At.byte hb4)).append (At.byte hb5)).append (At.byte hb6)).append (At.byte hb7)).append (At.byte hb8))
                                  have heq : [b1, b2, b3, b4, b5, b6, b7, b8] = magicVersion := by
                                    simp only [magicVersion, List.cons.injEq]
                                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> apply UScalar.eq_of_val_eq <;> scalar_tac
                                  simpa [heq] using hbytes

end Itasca

end

/-! ## FramingComplete -/

section

/-!
# Completeness of section framing

Acceptance (`.complete`) of `metadata.have_bytes`, `metadata.copy_bytes`, `metadata.read_section_header`
and `metadata.read_header` from independent byte spans, and `At.section_split`, which recovers the
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

/-- `metadata.have_bytes` accepts when the bytes are available. -/
theorem metadata.have_bytes.complete (data : Slice U8) (pos n : Usize)
    (h : pos.val + n.val ≤ data.length) : metadata.have_bytes data pos n = .ok (.Ok ()) := by
  obtain ⟨r, hr, hgood, _⟩ := WP.spec_imp_exists
    (metadata.have_bytes.spec data pos n (by omega))
  exact (hgood.mpr h) ▸ hr

/-- Copying a known byte interval recovers its exact vector, including empty intervals. -/
theorem metadata.copy_bytes.complete (data : Slice U8) (first last : Usize)
    (out : alloc.vec.Vec U8) (h : Wasm1.BytesAt data first out.val last) :
    metadata.copy_bytes data first last = .ok out := by
  obtain ⟨result, hr, hs⟩ := WP.spec_imp_exists
    (metadata.copy_bytes.spec data first last (by have := h.length; omega) h.bound)
  have he : result = out := alloc.vec.Vec.ext _ _
    (List.append_cancel_right (hs.suffix.symm.trans h.suffix))
  simpa [he] using hr

/-- `metadata.read_section_header` accepts a `SectionHeader` span and returns its id and bounds. -/
theorem metadata.read_section_header.complete (data : Slice U8) (pos : Usize)
    (id : U8) (first last : Usize) (h : SectionHeader data pos id first last) :
    metadata.read_section_header data pos = .ok (.Ok (id, first, last)) := by
  obtain ⟨middle, count, hid, hc, hlast, hbound⟩ := h
  have hr := hid.read_byte
  have hcount := reader.read_u32_leb.complete data middle count first hc
  have hs : metadata.read_section_header data pos ⦃ r => r = .Ok (id, first, last) ⦄ := by
    simp [metadata.read_section_header, hr, hcount, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hb : first.val + n.val ≤ data.length := by scalar_tac
    rw [metadata.have_bytes.complete data first n hb]
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

/-- `metadata.read_header` accepts the magic and version bytes. -/
theorem metadata.read_header.complete (data : Slice U8) (next : Usize)
    (h : Wasm1.BytesAt data 0#usize magicVersion next) :
    metadata.read_header data = .ok (.Ok next) := by
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
  simp [metadata.read_header, h0, h1, h2, h3, h4, h5, h6, h7,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## Copies -/

section

/-!
# Copying and looking up types

Specs for the allocation helpers `metadata.copy_value_types`, `metadata.copy_func_type` (each returns
a copy equal to its source) and `metadata.lookup_type` (the indexed type, or `UnknownType` when the
index is out of range).
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The copy loop appends the remaining source elements to `out` in order. -/
@[step]
theorem metadata.copy_value_types_loop.spec (src : Slice wasm_types.ValueType)
    (out : alloc.vec.Vec wasm_types.ValueType) (i : Usize)
    (hi : i.val ≤ src.val.length)
    (hsize : out.val.length + (src.val.length - i.val) ≤ Usize.max) :
    metadata.copy_value_types_loop src out i ⦃ copied =>
      copied.val = out.val ++ src.val.drop i.val ⦄ := by
  unfold metadata.copy_value_types_loop
  apply loop.spec_decr_nat (fun p => src.val.length - p.2.val)
    (fun p => p.2.val ≤ src.val.length ∧
      p.1.val ++ src.val.drop p.2.val = out.val ++ src.val.drop i.val ∧
      p.1.val.length + (src.val.length - p.2.val) ≤ Usize.max)
  · rintro ⟨v, j⟩ ⟨hj, hv, hb⟩
    dsimp only at hj hv hb
    unfold metadata.copy_value_types_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = src.val.length := by scalar_tac
      simp [heq] at hv
      simp [hv]
    · rename_i hmore
      have hlt : j.val < src.val.length := by scalar_tac
      have hcapacity : v.val.length < Usize.max := by omega
      step
      step
      step
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [out1_post, i2_post, vt_post, ← hv]
      simp only [List.append_assoc, List.singleton_append]
      rw [List.drop_eq_getElem_cons hlt]
  · exact ⟨hi, rfl, hsize⟩

/-- `metadata.copy_value_types` returns a vector equal to its source. -/
@[step]
theorem metadata.copy_value_types.spec (src : Slice wasm_types.ValueType) :
    metadata.copy_value_types src ⦃ copied => copied.val = src.val ⦄ := by
  simpa [metadata.copy_value_types] using
    metadata.copy_value_types_loop.spec src (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp)

/-- `metadata.copy_func_type` returns a function type equal to its source. -/
@[step]
theorem metadata.copy_func_type.spec (ft : wasm_types.FuncType) :
    metadata.copy_func_type ft ⦃ copied => copied = ft ⦄ := by
  unfold metadata.copy_func_type
  obtain ⟨p, hp, hpval⟩ := WP.spec_imp_exists
    (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.params))
  obtain ⟨r, hr, hrval⟩ := WP.spec_imp_exists
    (metadata.copy_value_types.spec (alloc.vec.Vec.deref ft.results))
  have hp' : p = ft.params := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hpval)
  have hr' : r = ft.results := alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.deref] using hrval)
  simp [hp, hr, hp', hr']

/-- `metadata.lookup_type` returns the type at the index, or `UnknownType` exactly when the index is
out of range. -/
@[step]
theorem metadata.lookup_type.spec (env : metadata.Env) (idx : U32) :
    metadata.lookup_type env idx ⦃ r =>
      match r with
      | .Ok ft => ∃ hi : idx.val < env.types.val.length, env.types.val[idx.val] = ft
      | .Err e => e = .UnknownType idx ∧ env.types.val.length ≤ idx.val ⦄ := by
  unfold metadata.lookup_type
  step*

end Itasca

end

/-! ## SegmentIndex -/

section

/-!
# Segment index decoder

Soundness (`profile_spec`) and acceptance (`profile_complete`) of `metadata.decode_segment_index`,
which reads the optional explicit table or memory index of an active segment according to
`SegmentIndexEncoding`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- `metadata.decode_segment_index` returns the index, next cursor and whether the index was
explicit, with the bytes consumed matching `SegmentIndexEncoding` for the flag word. -/
theorem metadata.decode_segment_index.profile_spec (data : Slice U8) (pos : Usize)
    (flags : U32) (hpos : pos.val ≤ data.length) :
    metadata.decode_segment_index data pos flags ⦃ r => match r with
      | .Ok (idx, next, explicit) =>
          At (fun pair => SegmentIndexEncoding flags pair.1 pair.2)
            data pos (idx, explicit) next
      | .Err _ => True ⦄ := by
  by_cases hzero : flags = 0#u32
  · subst flags
    simp only [metadata.decode_segment_index]
    exact ⟨[], Or.inl ⟨rfl, rfl, rfl, rfl⟩, Wasm1.BytesAt.nil data pos hpos⟩
  · by_cases htwo : flags = 2#u32
    · subst flags
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      cases r with
      | Err e =>
          simp [metadata.decode_segment_index, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨idx, next⟩ := pair
          simp only [metadata.decode_segment_index, hr, core.result.Result.Insts.CoreOpsTry.branch,
            bind_ok]
          obtain ⟨bytes, he, hs⟩ := At.of_u32 hp
          exact ⟨bytes, Or.inr ⟨rfl, rfl, he⟩, hs⟩
    · have h0 : flags.val ≠ 0 := fun h => hzero (UScalar.eq_of_val_eq h)
      have h2 : flags.val ≠ 2 := fun h => htwo (UScalar.eq_of_val_eq h)
      simp only [metadata.decode_segment_index]
      split
      · exact (h0 rfl).elim
      · exact (h2 rfl).elim
      · simp

/-- `metadata.decode_segment_index` accepts any independent `SegmentIndexEncoding` span. -/
theorem metadata.decode_segment_index.profile_complete {data : Slice U8} {pos next : Usize}
    {flags idx : U32} {explicit : Bool}
    (h : At (fun pair => SegmentIndexEncoding flags pair.1 pair.2)
      data pos (idx, explicit) next) :
    metadata.decode_segment_index data pos flags = .ok (.Ok (idx, next, explicit)) := by
  obtain ⟨bytes, he, hs⟩ := h
  rcases he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, he⟩
  · rw [hs.empty]
    rfl
  · simp [metadata.decode_segment_index, hs.read_u32 idx he,
      core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## Utf8 -/

section

/-!
# UTF-8 validation

`metadata.validate_utf8.spec`: an accepted byte string satisfies the independent strict `Utf8`
predicate (canonical encodings of Unicode scalar values, including four-byte sequences). The
helpers `metadata.utf8_cont` and `metadata.utf8_sequence_len` get their own specs. Completeness is in
`Module/Readers/Utf8Complete`.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 1200000

namespace Itasca.ModuleBinary

/-- The `count` bytes at `pos` are in range and form one canonical UTF-8 character. -/
def Utf8Sequence (bytes : Slice U8) (pos count : Usize) : Prop :=
  pos.val + count.val ≤ bytes.length ∧ 0 < count.val ∧
    Utf8Char ((bytes.val.drop pos.val).take count.val)

/-- UTF-8 validity is closed under concatenation. -/
theorem Utf8.append {first rest} (h : Utf8 first) (h' : Utf8 rest) : Utf8 (first ++ rest) := by
  induction h with
  | nil => simpa using h'
  | cons hc _ ih => simpa [List.append_assoc] using Utf8.cons hc ih

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary

private theorem take_one (xs : List U8) (i : Nat) (hb : i < xs.length) :
    (xs.drop i).take 1 = [xs[i]] := by
  rw [List.drop_eq_getElem_cons hb, List.take, List.take]

private theorem take_two (xs : List U8) (i : Nat) (hb : i + 1 < xs.length) :
    (xs.drop i).take 2 = [xs[i]'(by omega), xs[i + 1]] := by
  rw [List.drop_eq_getElem_cons (by omega : i < xs.length)]
  simp only [List.take_succ_cons]
  rw [take_one xs (i + 1) hb]

private theorem take_three (xs : List U8) (i : Nat) (hb : i + 2 < xs.length) :
    (xs.drop i).take 3 = [xs[i]'(by omega), xs[i + 1]'(by omega), xs[i + 2]] := by
  rw [List.drop_eq_getElem_cons (by omega : i < xs.length)]
  simp only [List.take_succ_cons]
  rw [take_two xs (i + 1) (by omega)]

private theorem take_four (xs : List U8) (i : Nat) (hb : i + 3 < xs.length) :
    (xs.drop i).take 4 = [xs[i]'(by omega), xs[i + 1]'(by omega), xs[i + 2]'(by omega), xs[i + 3]] := by
  rw [List.drop_eq_getElem_cons (by omega : i < xs.length)]
  simp only [List.take_succ_cons]
  rw [take_three xs (i + 1) (by omega)]

/-- An accepted `metadata.utf8_cont` found an in-range byte between `lo` and `hi`. -/
@[step]
theorem metadata.utf8_cont.spec (bytes : Slice U8) (pos : Usize) (lo hi : U8) :
    metadata.utf8_cont bytes pos lo hi ⦃ r => r = .Ok () →
      ∃ hb : pos.val < bytes.length, lo.val ≤ bytes.val[pos.val].val ∧ bytes.val[pos.val].val ≤ hi.val ⦄ := by
  unfold metadata.utf8_cont
  step*

/-- `metadata.utf8_sequence_len` returns the length of one valid UTF-8 character at `pos`. -/
theorem metadata.utf8_sequence_len.spec (bytes : Slice U8) (pos : Usize)
    (hb : pos.val < bytes.length) :
    metadata.utf8_sequence_len bytes pos ⦃ r => match r with
      | .Ok count => Utf8Sequence bytes pos count
      | .Err _ => True ⦄ := by
  unfold metadata.utf8_sequence_len
  step
  split <;> step*
  all_goals try casesm* core.result.Result Unit error.Error
  all_goals simp_all
  all_goals have hbval := congrArg UScalar.val b_post
  all_goals clear b_post
  all_goals try simp only [show (224#8#uscalar : U8).val = 224 from rfl,
    show (237#8#uscalar : U8).val = 237 from rfl,
    show (240#8#uscalar : U8).val = 240 from rfl,
    show (244#8#uscalar : U8).val = 244 from rfl] at *
  all_goals try casesm* (∃ _, _), (_ ∧ _)
  all_goals try scalar_tac
  all_goals unfold Utf8Sequence
  all_goals refine ⟨by scalar_tac, by scalar_tac, ?_⟩
  all_goals simp only [UScalar.ofNatCore_val_eq]
  all_goals first
    | (rw [take_one bytes.val pos.val (by scalar_tac)]; apply Utf8Char.one; scalar_tac)
    | (rw [take_two bytes.val pos.val (by scalar_tac)]; apply Utf8Char.two <;> scalar_tac)
    | (rw [take_three bytes.val pos.val (by scalar_tac)]; apply Utf8Char.three <;> scalar_tac)
    | (rw [take_four bytes.val pos.val (by scalar_tac)]; apply Utf8Char.four <;> scalar_tac)

/-- `metadata.validate_utf8` returns normally, and acceptance implies `Utf8`. -/
@[step]
theorem metadata.validate_utf8.spec (bytes : Slice U8) :
    metadata.validate_utf8 bytes ⦃ r => r = .Ok () → Utf8 bytes.val ⦄ := by
  unfold metadata.validate_utf8 metadata.validate_utf8_loop
  apply loop.spec_decr_nat (fun i => bytes.length - i.val)
    (fun i => i.val ≤ bytes.length ∧ Utf8 (bytes.val.take i.val))
  · intro pos hp
    obtain ⟨hb, hprefix⟩ := hp
    by_cases hend : bytes.length ≤ pos.val
    · have heq : pos.val = bytes.length := by omega
      have hd : pos ≥ Slice.len bytes := by scalar_tac
      simp [metadata.validate_utf8_loop.body, hd]
      simpa [heq] using hprefix
    · have hlt : pos.val < bytes.length := by omega
      have hd : ¬pos ≥ Slice.len bytes := by scalar_tac
      obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (metadata.utf8_sequence_len.spec bytes pos hlt)
      cases r with
      | Err e =>
          simp [metadata.validate_utf8_loop.body, hd, hr,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok count =>
          obtain ⟨hbound, hpositive, hchar⟩ := hs
          simp [metadata.validate_utf8_loop.body, hd, hr,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [i2_post, List.take_add]
          exact hprefix.append (by simpa using Utf8.cons hchar Utf8.nil)
  · exact ⟨by simp, by simpa using Utf8.nil⟩

end Itasca

end
