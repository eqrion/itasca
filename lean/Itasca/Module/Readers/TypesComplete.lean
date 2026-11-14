import Itasca.Module.Readers.Utf8

/-!
Sections, each formerly its own module: Names, Utf8Complete, NamesComplete, TypesComplete.
-/

/-! ## Names -/

section

/-!
# Name and custom section readers

`metadata.decode_name.spec`: an accepted name is a length-prefixed byte vector of valid UTF-8.
`metadata.decode_custom_section.spec`: the name lies within the section and the rest of the payload
is an uninterpreted interval. Completeness is in `Module/Readers/NamesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- An accepted name is a `NameEncoding` span and its bytes are returned unchanged. -/
@[step]
theorem metadata.decode_name.spec (data : Slice U8) (start : Usize) :
    metadata.decode_name data start ⦃ r => match r with
      | .Ok (value, next) => At NameEncoding data start value.val next
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_name, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨len, pos⟩ := pair
      have hspan := hd.span
      simp [metadata.decode_name, hr, core.result.Result.Insts.CoreOpsTry.branch]
      step*
      cases r1 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          have hbound := r1_post.mp rfl
          simp only [bind_ok]
          step*
          cases r2 with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              simp only [bind_ok, WP.spec_ok]
              have hutf := r2_post rfl
              have hlength : bytes.val.length = len.val := by
                have := bytes_post.length
                scalar_tac
              obtain ⟨countBytes, hs, hl, hb, he⟩ := hd
              refine ⟨countBytes ++ bytes.val, ⟨?_, by simpa [alloc.vec.Vec.deref] using hutf⟩, ?_⟩
              · exact ByteVecEncoding.iff.mpr ⟨countBytes, by simpa [hlength] using he, rfl⟩
              · exact (show Wasm1.BytesAt data start countBytes pos from ⟨hs, hl, hb⟩).append bytes_post

/-- The custom section name is a `NameEncoding` span within the section. The returned metadata
gives the name length and the payload interval from the end of the name to `last`. -/
@[step]
theorem metadata.decode_custom_section.spec (data : Slice U8) (start last : Usize) :
    metadata.decode_custom_section data start last ⦃ r => match r with
      | .Ok custom => ∃ nm, At NameEncoding data start nm custom.payload_start ∧
          custom.payload_start.val ≤ last.val ∧ custom.payload_end = last ∧
          custom.name_len.val = nm.length
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (metadata.decode_name.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_custom_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨nm, next⟩ := pair
      simp [metadata.decode_custom_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
      split
      · simp
      · rename_i hbound
        simp only [WP.spec_ok]
        exact ⟨nm.val, hd, by scalar_tac, trivial, rfl⟩

end Itasca

end

/-! ## Utf8Complete -/

section

/-!
# Completeness of UTF-8 validation

`metadata.validate_utf8.complete`: the scanner accepts every independent `Utf8` byte string, through
`metadata.utf8_sequence_len.complete` and `metadata.validate_utf8_loop.complete`. Soundness is in
`Module/Readers/Utf8`.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 1600000

namespace Itasca.Wasm1

/-- Indexing a `BytesAt` span reads the corresponding input byte. -/
theorem BytesAt.get {data start bytes next} (h : BytesAt data start bytes next)
    (i : Nat) (hi : i < bytes.length) :
    data.val[start.val + i]'(by have := h.length; have := h.bound; scalar_tac) = bytes[i] := by
  have hd : i < (data.val.drop start.val).length := by
    simp only [List.length_drop]
    have := h.length
    have := h.bound
    scalar_tac
  have he : (data.val.drop start.val)[i] = bytes[i] := by
    simp only [h.suffix, List.getElem_append_left hi]
  simpa only [List.getElem_drop] using he

end Itasca.Wasm1

namespace Itasca
open ModuleBinary

@[local step] private theorem utf8_cont_accepts (data : Slice U8) (pos : Usize) (lo hi : U8)
    (hp : pos.val < data.length)
    (hl : lo.val ≤ data.val[pos.val].val) (hh : data.val[pos.val].val ≤ hi.val) :
    metadata.utf8_cont data pos lo hi ⦃ r => r = .Ok () ⦄ := by
  unfold metadata.utf8_cont
  step*

/-- `metadata.utf8_sequence_len` accepts one canonical UTF-8 character and returns its length. -/
theorem metadata.utf8_sequence_len.complete (data : Slice U8) (pos next : Usize)
    (encoded : List U8) (hc : Utf8Char encoded) (hb : Wasm1.BytesAt data pos encoded next) :
    ∃ count, metadata.utf8_sequence_len data pos = .ok (.Ok count) ∧ count.val = encoded.length := by
  have hs : metadata.utf8_sequence_len data pos ⦃ r =>
      ∃ count, r = .Ok count ∧ count.val = encoded.length ⦄ := by
    have hlen := hb.length
    have hbound := hb.bound
    have heqval (a b : U8) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    cases hc with
    | one a ha =>
        have h0 := hb.get 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        unfold metadata.utf8_sequence_len
        step
        split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
    | two a b ha ha' hb0 hb1 =>
        have h0 := hb.get 0 (by simp)
        have h1 := hb.get 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
        unfold metadata.utf8_sequence_len
        step
        split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
    | three a b c ha hc0 hc1 =>
        have h0 := hb.get 0 (by simp)
        have h1 := hb.get 1 (by simp)
        have h2 := hb.get 2 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2
        rcases ha with ha | ha | ha | ha
        all_goals unfold metadata.utf8_sequence_len
        all_goals step
        all_goals split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
    | four a b c d ha hc0 hc1 hd0 hd1 =>
        have h0 := hb.get 0 (by simp)
        have h1 := hb.get 1 (by simp)
        have h2 := hb.get 2 (by simp)
        have h3 := hb.get 3 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3
        rcases ha with ha | ha | ha
        all_goals unfold metadata.utf8_sequence_len
        all_goals step
        all_goals split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
  obtain ⟨r, hr, count, rfl, hc⟩ := WP.spec_imp_exists hs
  exact ⟨count, hr, hc⟩


/-- The scan loop accepts a valid UTF-8 suffix that runs to the end of the input. -/
theorem metadata.validate_utf8_loop.complete (data : Slice U8) (pos : Usize)
    (encoded : List U8) (hc : Utf8 encoded)
    (hb : Wasm1.BytesAt data pos encoded (Slice.len data)) :
    metadata.validate_utf8_loop data pos = .ok (.Ok ()) := by
  induction hc generalizing pos with
  | nil =>
      have he := hb.empty
      subst pos
      unfold metadata.validate_utf8_loop
      rw [loop]
      simp [metadata.validate_utf8_loop.body]
  | @cons first rest hchar hrest ih =>
      obtain ⟨middle, hfirst, htail⟩ := hb.split
      have hpositive : 0 < first.length := by cases hchar <;> simp
      have hmore : ¬ pos ≥ Slice.len data := by
        have := hfirst.length
        have := hfirst.bound
        scalar_tac
      obtain ⟨count, hcount, hlen⟩ := metadata.utf8_sequence_len.complete data pos middle first hchar hfirst
      obtain ⟨next, hnext, hn⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := pos) (y := count) (by have := hfirst.length; scalar_tac))
      have he : next = middle := UScalar.eq_of_val_eq (by have := hfirst.length; omega)
      subst next
      have hbody : metadata.validate_utf8_loop.body data pos = .ok (.cont middle) := by
        simp [metadata.validate_utf8_loop.body, hmore, hcount, hnext,
          core.result.Result.Insts.CoreOpsTry.branch]
      have hloop := ih middle htail
      unfold metadata.validate_utf8_loop at hloop ⊢
      rw [loop]
      simp only [hbody, bind_ok]
      exact hloop

/-- `metadata.validate_utf8` accepts every `Utf8` byte string, including all Unicode scalar values
through U+10FFFF. -/
theorem metadata.validate_utf8.complete (data : Slice U8) (h : Utf8 data.val) :
    metadata.validate_utf8 data = .ok (.Ok ()) := by
  apply metadata.validate_utf8_loop.complete data 0#usize data.val h
  constructor <;> simp

end Itasca

end

/-! ## NamesComplete -/

section

/-!
# Completeness of name readers

Acceptance of `metadata.decode_name` and `metadata.decode_custom_section` from independent name
encodings (`.complete`, and `.complete_raw` for a name given as a list). Strict UTF-8 acceptance
comes from `Module/Readers/Utf8Complete`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- Given a byte vector span and the UTF-8 scanner's reply on the copied name,
`metadata.decode_name` returns that reply's verdict with the name and cursor. -/
theorem metadata.decode_name.from_utf8 (data : Slice U8) (pos : Usize)
    (nm : alloc.vec.Vec U8) (next : Usize)
    (h : At ByteVecEncoding data pos nm.val next)
    (reply : core.result.Result Unit error.Error)
    (hutf8 : metadata.validate_utf8 (alloc.vec.Vec.deref nm) = .ok reply) :
    metadata.decode_name data pos = .ok (match reply with
      | .Ok _ => .Ok (nm, next)
      | .Err e => .Err e) := by
  obtain ⟨count, middle, hcount, hlen, encoded, hrep, hbytes⟩ := h.vector_split
  have hb : Wasm1.BytesAt data middle nm.val next := by simpa only [hrep.bytes] using hbytes
  have hr := reader.read_u32_leb.complete data pos count middle hlen
  have hs : metadata.decode_name data pos ⦃ r => r = (match reply with
      | .Ok _ => .Ok (nm, next)
      | .Err e => .Err e) ⦄ := by
    simp [metadata.decode_name, hr, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hroom : middle.val + n.val ≤ data.length := by have := hb.length; have := hb.bound; scalar_tac
    rw [metadata.have_bytes.complete data middle n hroom]
    simp only [bind_ok]
    step
    have hend : i = next := UScalar.eq_of_val_eq (by have := hb.length; scalar_tac)
    rw [hend, metadata.copy_bytes.complete data middle next nm hb]
    simp only [bind_ok, hutf8]
    cases reply <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- `metadata.decode_name` accepts a `NameEncoding` span and returns the name and cursor. -/
theorem metadata.decode_name.complete (data : Slice U8) (pos : Usize)
    (nm : alloc.vec.Vec U8) (next : Usize) (h : At NameEncoding data pos nm.val next) :
    metadata.decode_name data pos = .ok (.Ok (nm, next)) := by
  obtain ⟨bytes, ⟨hvec, hutf8⟩, hs⟩ := h
  exact metadata.decode_name.from_utf8 data pos nm next ⟨bytes, hvec, hs⟩ (.Ok ())
    (metadata.validate_utf8.complete _ (by simpa [alloc.vec.Vec.deref] using hutf8))

/-- `metadata.decode_name.complete` for a name given as a list: the returned vector has those
bytes. -/
theorem metadata.decode_name.complete_raw (data : Slice U8) (pos : Usize)
    (nm : List U8) (next : Usize) (h : At NameEncoding data pos nm next) :
    ∃ value, metadata.decode_name data pos = .ok (.Ok (value, next)) ∧ value.val = nm := by
  have hsize : nm.length ≤ Usize.max := by
    obtain ⟨bytes, ⟨hvec, _⟩, _⟩ := h
    obtain ⟨count, _, hc, _, _⟩ := hvec
    have := hc.value_lt
    scalar_tac
  let value := alloc.vec.Vec.from nm hsize
  exact ⟨value, metadata.decode_name.complete data pos value next (by simpa [value] using h), by simp [value]⟩

/-- `metadata.decode_custom_section.complete` for a name given as a list. -/
theorem metadata.decode_custom_section.complete_raw (data : Slice U8) (pos next last : Usize)
    (nm : List U8) (h : At NameEncoding data pos nm next) (hbefore : next.val ≤ last.val) :
    ∃ custom, metadata.decode_custom_section data pos last = .ok (.Ok custom) ∧
      custom.name_len.val = nm.length ∧ custom.payload_start = next ∧ custom.payload_end = last := by
  obtain ⟨value, hr, hv⟩ := metadata.decode_name.complete_raw data pos nm next h
  refine ⟨⟨alloc.vec.Vec.len value, next, last⟩, ?_, by simpa using congrArg List.length hv, rfl, rfl⟩
  simp [metadata.decode_custom_section, hr, hbefore, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## TypesComplete -/

section

/-!
# Completeness of the type readers

Acceptance (`.complete`) of `limits.validate_limits`, `metadata.decode_limits`,
`metadata.decode_mem_type`, `metadata.decode_table_type`, `metadata.decode_global_type`,
`metadata.decode_value_types` and `metadata.decode_func_type` from independent encodings that satisfy
the limit bounds and signature caps. Soundness is in
`Module/Readers/Types`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

/-- `limits.validate_limits` accepts limits satisfying `LimitsValid`. -/
theorem limits.validate_limits.complete (lim : wasm_types.Limits) (bound : U32)
    (h : LimitsValid lim bound) : limits.validate_limits lim bound = .ok (.Ok ()) := by
  obtain ⟨hmin, hmax⟩ := h
  have hmin' : ¬lim.min > bound := by scalar_tac
  unfold limits.validate_limits
  simp only [hmin', ↓reduceIte]
  cases he : lim.max with
  | none => rfl
  | some maximum =>
      obtain ⟨hlo, hhi⟩ := hmax maximum he
      have hhi' : ¬maximum > bound := by scalar_tac
      have hlo' : ¬lim.min > maximum := by scalar_tac
      simp [hhi', hlo']

/-- `metadata.decode_limits` accepts a `LimitsEncoding` span. -/
theorem metadata.decode_limits.complete (data : Slice U8) (pos : Usize)
    (lim : wasm_types.Limits) (next : Usize) (h : At LimitsEncoding data pos lim next) :
    metadata.decode_limits data pos = .ok (.Ok (lim, next)) := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he with
  | noMax minimum hb =>
      obtain ⟨middle, htag, hbytes⟩ := (show Wasm1.BytesAt data pos ([0#u8] ++ _) next from hs).split
      simp [metadata.decode_limits, htag.read_byte, hbytes.read_u32 minimum hb,
        core.result.Result.Insts.CoreOpsTry.branch]
  | max minimum maximum hlo hhi =>
      obtain ⟨first, htag, hbytes⟩ := (show Wasm1.BytesAt data pos ([1#u8] ++ _) next from hs).split
      obtain ⟨middle, hl, hh⟩ := hbytes.split
      simp [metadata.decode_limits, htag.read_byte, hl.read_u32 minimum hlo,
        hh.read_u32 maximum hhi, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_global_type` accepts a `GlobalTypeEncoding` span. -/
theorem metadata.decode_global_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.GlobalType) (next : Usize) (h : At GlobalTypeEncoding data pos ty next) :
    metadata.decode_global_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  obtain ⟨middle, hvalue, hmut⟩ :=
    (show Wasm1.BytesAt data pos ([valueByte ty.valtype] ++ [mutByte ty.mutability]) next from hs).split
  have hv := metadata.decode_value_type.complete data pos ty.valtype middle ⟨_, rfl, hvalue⟩
  have hm := hmut.read_byte
  cases ty with
  | mk mutability valtype =>
      cases mutability <;> simp [metadata.decode_global_type, hv, hm, mutByte,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_mem_type` accepts a `MemTypeEncoding` span with limits within
`limits.MAX_MEMORY_PAGES`. -/
theorem metadata.decode_mem_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.MemType) (next : Usize) (h : At MemTypeEncoding data pos ty next)
    (hv : LimitsValid ty.limits limits.MAX_MEMORY_PAGES) :
    metadata.decode_mem_type data pos = .ok (.Ok (ty, next)) := by
  have hr := metadata.decode_limits.complete data pos ty.limits next h
  have hc := limits.validate_limits.complete ty.limits limits.MAX_MEMORY_PAGES hv
  cases ty
  simp [metadata.decode_mem_type, hr, hc, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_table_type` accepts a `TableTypeEncoding` span with limits within
`limits.MAX_TABLE_ELEMS`. -/
theorem metadata.decode_table_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.TableType) (next : Usize) (h : At TableTypeEncoding data pos ty next)
    (hv : LimitsValid ty.limits limits.MAX_TABLE_ELEMS) :
    metadata.decode_table_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, ⟨limitBytes, hl, rfl⟩, hs⟩ := h
  obtain ⟨middle, htag, hbytes⟩ := (show Wasm1.BytesAt data pos ([elemByte ty.elem] ++ limitBytes) next from hs).split
  have hr := metadata.decode_limits.complete data middle ty.limits next ⟨_, hl, hbytes⟩
  have hc := limits.validate_limits.complete ty.limits limits.MAX_TABLE_ELEMS hv
  have ht := metadata.decode_elem_type.complete data pos ty.elem middle ⟨_, rfl, htag⟩
  cases ty
  simp [metadata.decode_table_type, ht, hr, hc, core.result.Result.Insts.CoreOpsTry.branch]


/-- The counted loop accepts an encoded suffix of value types and appends them to the accumulated
`out`, provided the remaining count and capacity fit. -/
theorem metadata.decode_value_types_loop.complete (data : Slice U8) (count : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (pos : Usize) (i : U32)
    (values : List wasm_types.ValueType) (next : Usize)
    (hbytes : At (Rep ValueTypeEncoding) data pos values next)
    (hcount : i.val + values.length = count.val)
    (hcapacity : out.val.length + values.length ≤ Usize.max) :
    ∃ final, metadata.decode_value_types_loop data count out pos i = .ok (.Ok (final, next)) ∧
      final.val = out.val ++ values := by
  induction values generalizing out pos i with
  | nil =>
      have hend := hbytes.rep_nil
      subst next
      have hstop : i ≥ count := by simpa using (show count.val ≤ i.val by simpa using hcount.symm.le)
      refine ⟨out, ?_, by simp⟩
      unfold metadata.decode_value_types_loop
      rw [loop]
      simp [metadata.decode_value_types_loop.body, hstop]
  | cons value values ih =>
      obtain ⟨middle, hfirst, hrest⟩ := hbytes.rep_cons
      have hread := metadata.decode_value_type.complete data pos value middle hfirst
      have hmore : ¬i ≥ count := by scalar_tac
      have hroom : out.val.length < Usize.max := by simp only [List.length_cons] at hcapacity; omega
      obtain ⟨updated, hpush, hout⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out value hroom)
      obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
        (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      obtain ⟨final, hloop, hfinal⟩ := ih updated middle j hrest
        (by simp only [List.length_cons] at hcount; scalar_tac)
        (by simp only [hout, List.length_append, List.length_cons, List.length_nil] at *; omega)
      refine ⟨final, ?_, by simpa [hout, List.append_assoc] using hfinal⟩
      have hbody : metadata.decode_value_types_loop.body data count out pos i =
          .ok (.cont (updated, middle, j)) := by
        simp [metadata.decode_value_types_loop.body, hmore, hread,
          core.result.Result.Insts.CoreOpsTry.branch, hpush, hj]
      unfold metadata.decode_value_types_loop at hloop ⊢
      rw [loop]
      dsimp only
      rw [hbody]
      simpa only [bind_ok] using hloop

/-- `metadata.decode_value_types` accepts a vector span of value types within the length
bound. -/
theorem metadata.decode_value_types.complete (data : Slice U8) (pos : Usize)
    (values : alloc.vec.Vec wasm_types.ValueType) (next : Usize) (limit : Usize) (err : error.OpError)
    (h : At (VecEncoding ValueTypeEncoding) data pos values.val next)
    (hbound : values.val.length ≤ limit.val) :
    metadata.decode_value_types data pos limit err = .ok (.Ok (values, next)) := by
  obtain ⟨count, middle, hcount, hlen, hbytes⟩ := h.vector_split
  have hr := reader.read_u32_leb.complete data pos count middle hlen
  obtain ⟨final, hf, he⟩ := metadata.decode_value_types_loop.complete data count
    (alloc.vec.Vec.new _) middle 0#u32 values.val next hbytes
    (by simpa using hcount.symm) (by simp)
  have heq : final = values := alloc.vec.Vec.ext _ _ (by simpa using he)
  have hfits : ¬ count.val > limit.val := by omega
  simp [metadata.decode_value_types, hr, hf, heq, core.result.Result.Insts.CoreOpsTry.branch,
    lift, hfits]

/-- `metadata.decode_func_type` accepts a `FuncTypeEncoding` span that satisfies the signature cap. -/
theorem metadata.decode_func_type.profile_complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.FuncType) (next : Usize)
    (h : At FuncTypeEncoding data pos ty next)
    (hlimits : Profile.FuncTypeWithinLimits ty) :
    metadata.decode_func_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, ⟨params, results, hp, hr, rfl⟩, hs⟩ := h
  obtain ⟨first, htag, hbytes⟩ :=
    (show Wasm1.BytesAt data pos ([0x60#u8] ++ (params ++ results)) next from hs).split
  obtain ⟨middle, hparams, hresultsBytes⟩ := hbytes.split
  have hp' := metadata.decode_value_types.complete data first ty.params middle
    limits.MAX_MULTI_VALUE_PARAMS error.OpError.TooManyParams ⟨params, hp, hparams⟩ hlimits.1

  have hr' := metadata.decode_value_types.complete data middle ty.results next
    limits.MAX_MULTI_VALUE_RESULTS error.OpError.TooManyResults ⟨results, hr, hresultsBytes⟩ hlimits.2

  cases ty
  simp [metadata.decode_func_type, htag.read_byte, hp', hr',
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end
