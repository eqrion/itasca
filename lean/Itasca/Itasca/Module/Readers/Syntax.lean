import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Binary.ModuleUnique
import Itasca.Binary.Scalar.Encoding
import Itasca.Support.Translation

/-!
Proofs for Module / Readers.

This module collects Primitives, Syntax.
Each section documents its contracts and consumers.
-/

/-! ## Primitives -/

section

/-!
# Primitive module-reader contracts

Byte/index spans, bounds, section headers and value/signature/limit readers establish
independent encoding postconditions. Higher section parsers compose these contracts.
-/

/-! ## Basic -/

section

/-!
# Primitive module readers

Soundness specs for the byte-level helpers of the module parser: `reader.read_byte`,
`metadata.have_bytes`, `metadata.copy_bytes`, `metadata.read_section_header`, `limits.validate_limits`,
`metadata.decode_value_type` and `metadata.decode_elem_type`. Each relates a successful result to the
independent grammar through `ParserPost`, or states `SectionHeader` and `LimitsValid`. Completeness
is in `Module/Readers/Syntax`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A parser result is either an error, or a value and next cursor with `At R data start value
next`. It carries no guarantee for errors. -/
def ParserPost {α : Type} (R : α → List U8 → Prop) (data : Slice U8) (start : Usize) :
    core.result.Result (α × Usize) error.Error → Prop
  | .Ok (value, next) => At R data start value next
  | .Err _ => True

/-- A decoded `u32` is an `IndexEncoding`. -/
theorem At.of_u32 {data start value next} (h : Binary.Leb128.Decoded data start value next) :
    At IndexEncoding data start value next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := h
  exact ⟨bytes, he, hs, hl, hb⟩

/-- A one-byte encoding covers exactly that byte. -/
theorem At.byte {data start byte next}
    (h : At ByteEncoding data start byte next) : Body.Scalar.BytesAt data start [byte] next := by
  obtain ⟨bytes, rfl, hs⟩ := h
  exact hs

/-- A byte followed by an `R` encoding is an `S` encoding when `R` extended by that byte implies
`S`. -/
theorem At.prepend {α : Type} {R S : α → List U8 → Prop} {data start pos next b value}
    (hb : At ByteEncoding data start b pos) (hr : At R data pos value next)
    (hR : ∀ bytes, R value bytes → S value (b :: bytes)) : At S data start value next := by
  obtain ⟨bytes, he, hs⟩ := hr
  exact ⟨b :: bytes, hR bytes he, by simpa using hb.byte.append hs⟩

/-- A limits pair has `min` within `bound` and, when `max` is present, `min ≤ max ≤ bound`. -/
def LimitsValid (lim : wasm_types.Limits) (bound : U32) : Prop :=
  lim.min.val ≤ bound.val ∧ ∀ maximum, lim.max = some maximum →
    lim.min.val ≤ maximum.val ∧ maximum.val ≤ bound.val

/-- The payload interval of a header is ordered and within the input. -/
theorem SectionHeader.span {data start id first last}
    (h : SectionHeader data start id first last) :
    start.val < first.val ∧ first.val ≤ last.val ∧ last.val ≤ data.length := by
  obtain ⟨pos, size, hb, hd, hn, he⟩ := h
  have hs := hb.byte.length
  have hi := hd.span
  simp only [List.length_singleton] at hs
  omega

end Itasca.Binary

namespace Itasca

/-- `reader.read_byte` returns normally, and a byte read is a `ByteEncoding` span; reading at EOF
is an error. -/
theorem reader.read_byte.module_spec (data : Slice U8) (pos : Usize) :
    reader.read_byte data pos ⦃ r => match r with
      | .Ok (value, next) => Binary.At Binary.ByteEncoding data pos value next
      | .Err _ => True ⦄ := by
  by_cases hb : pos.val < data.length
  · apply WP.spec_mono (reader.read_byte.spec data pos hb)
    rintro r ⟨next, rfl, hn⟩
    exact ⟨_, rfl, Body.Scalar.BytesAt.byte data pos next _ hb rfl hn⟩
  · simp [reader.read_byte.eof data pos (by omega)]

/-- The subtraction-based bounds check terminates for an in-bounds cursor. -/
@[step]
theorem metadata.have_bytes.spec (data : Slice U8) (pos n : Usize)
    (hb : pos.val ≤ data.length) :
    metadata.have_bytes data pos n ⦃ r =>
      (r = .Ok () ↔ pos.val + n.val ≤ data.length) ∧
      (r = .Err .UnexpectedEof ↔ data.length < pos.val + n.val) ⦄ := by
  unfold metadata.have_bytes
  step* <;> scalar_tac

/-- `metadata.decode_value_type` returns a value type with its exact encoding. -/
@[step]
theorem metadata.decode_value_type.spec (data : Slice U8) (pos : Usize) :
    metadata.decode_value_type data pos ⦃ r =>
      Binary.ParserPost Binary.ValueTypeEncoding data pos r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
  cases r with
  | Err e =>
      simp [metadata.decode_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, Binary.ParserPost]
  | Ok pair =>
      obtain ⟨b, next⟩ := pair
      have hs := Binary.At.byte hp
      simp [metadata.decode_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        Binary.ParserPost]
      all_goals split
      all_goals first
        | exact ⟨_, Binary.ValueTypeEncoding.reader_bytes.mpr rfl, by with_unfolding_all exact hs⟩
        | simp

/-- `metadata.decode_elem_type` returns an element type with its exact encoding. -/
@[step]
theorem metadata.decode_elem_type.spec (data : Slice U8) (pos : Usize) :
    metadata.decode_elem_type data pos ⦃ r =>
      Binary.ParserPost Binary.ElemTypeEncoding data pos r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
  cases r with
  | Err e =>
      simp [metadata.decode_elem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, Binary.ParserPost]
  | Ok pair =>
      obtain ⟨b, next⟩ := pair
      have hs := Binary.At.byte hp
      simp [metadata.decode_elem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        Binary.ParserPost]
      all_goals split
      all_goals first
        | exact ⟨_, rfl, by with_unfolding_all exact hs⟩
        | simp

/-- `metadata.decode_value_type` returns a value type with its exact encoding. -/
theorem metadata.decode_value_type.syntax_spec (data : Slice U8) (pos : Usize) :
    metadata.decode_value_type data pos ⦃ r =>
      Binary.ParserPost Binary.ValueTypeEncoding data pos r ⦄ :=
  metadata.decode_value_type.spec data pos

private theorem copy_bytes_body (data : Slice U8) (last : Usize) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val < last.val) (hb : last.val ≤ data.length)
    (hlen : out.val.length ≤ i.val) :
    metadata.copy_bytes_loop.body data last out i ⦃ r =>
      ∃ out' next, r = .cont (out', next) ∧
        out'.val = out.val ++ [data.val[i.val]'(by simpa using Nat.lt_of_lt_of_le hi hb)] ∧ next.val = i.val + 1 ⦄ := by
  unfold metadata.copy_bytes_loop.body
  step*
  exact ⟨out1, i2, rfl, by simpa [i1_post] using out1_post, i2_post⟩

/-- Copying a bounded range terminates and returns exactly that byte interval. -/
@[step]
theorem metadata.copy_bytes.spec (data : Slice U8) (first last : Usize)
    (hf : first.val ≤ last.val) (hb : last.val ≤ data.length) :
    metadata.copy_bytes data first last ⦃ out => Body.Scalar.BytesAt data first out.val last ⦄ := by
  unfold metadata.copy_bytes metadata.copy_bytes_loop
  apply loop.spec_decr_nat (fun s => last.val - s.2.val)
    (fun s => first.val ≤ s.2.val ∧ s.2.val ≤ last.val ∧
      s.2.val = first.val + s.1.val.length ∧
      data.val.drop first.val = s.1.val ++ data.val.drop s.2.val)
  · rintro ⟨out, i⟩ ⟨hfirst, hlast, hlen, hs⟩
    dsimp only at *
    by_cases hdone : last.val ≤ i.val
    · have heq : i = last := UScalar.eq_of_val_eq (by omega)
      simp only [metadata.copy_bytes_loop.body, heq, ge_iff_le, le_refl, ↓reduceIte, WP.spec_ok]
      exact ⟨by simpa [heq] using hs, by simpa [heq] using hlen, hb⟩
    · apply WP.spec_mono (copy_bytes_body data last out i (by omega) hb (by omega))
      rintro _ ⟨out', next, rfl, hv, hn⟩
      dsimp only
      constructor
      · refine ⟨by omega, by omega, ?_, ?_⟩
        · simp only [hv, List.length_append, List.length_singleton]
          omega
        · rw [hs, List.drop_eq_getElem_cons (by omega : i.val < data.length), hv, hn]
          simp [List.append_assoc]
      · omega
  · simp [alloc.vec.Vec.new, hf]

/-- `limits.validate_limits` accepts only limits satisfying `LimitsValid`. -/
@[step]
theorem limits.validate_limits.spec (lim : wasm_types.Limits) (bound : U32) :
    limits.validate_limits lim bound ⦃ r => r = .Ok () → Binary.LimitsValid lim bound ⦄ := by
  unfold limits.validate_limits Binary.LimitsValid
  step*
  simp_all

/-- `metadata.read_section_header` returns a `SectionHeader` for the bytes it consumed. -/
theorem metadata.read_section_header.spec (data : Slice U8) (start : Usize) :
    metadata.read_section_header data start ⦃ r => match r with
      | .Ok (id, first, last) => Binary.SectionHeader data start id first last
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [metadata.read_section_header, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨id, pos⟩ := pair
      obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      cases r with
      | Err e =>
          simp [metadata.read_section_header, hr, hu, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨size, first⟩ := pair
          have hspan := hd.span
          simp [metadata.read_section_header, hr, hu,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          cases r2 with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              have hbound := r2_post.mp rfl
              simp only [bind_ok]
              step*
              exact ⟨pos, size, hp, hd, by scalar_tac, by scalar_tac⟩

end Itasca

end

/-! ## Types -/

section

/-!
# Limit, memory, table, global and function type readers

Soundness specs for `metadata.decode_limits`, `metadata.decode_mem_type`, `metadata.decode_table_type`,
`metadata.decode_global_type`, `metadata.decode_value_types` and `metadata.decode_func_type`. Results
are `At` spans of the independent grammar, together with the limit bounds.
Completeness is in `Module/Readers/Completeness`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Binary

/-- `metadata.decode_limits` returns a `LimitsEncoding` span. -/
@[step]
theorem metadata.decode_limits.spec (data : Slice U8) (start : Usize) :
    metadata.decode_limits data start ⦃ r => ParserPost LimitsEncoding data start r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_limits, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
  | Ok pair =>
      obtain ⟨flag, pos⟩ := pair
      by_cases hzero : flag = 0#u8
      · obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
        cases r with
        | Err e =>
            simp [metadata.decode_limits, hr, hu, hzero, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
        | Ok pair =>
            obtain ⟨min, next⟩ := pair
            simp [metadata.decode_limits, hr, hu, hzero, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
            obtain ⟨bytes, hs, hl, hb, he⟩ := hd
            refine ⟨0#u8 :: bytes, .noMax min.val ((Leb128.encoding_iff _ _).mp he), ?_⟩
            simpa [hzero] using (At.byte hp).append ⟨hs, hl, hb⟩
      · by_cases hone : flag = 1#u8
        · obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
          cases r with
          | Err e =>
              simp [metadata.decode_limits, hr, hu, hone, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
          | Ok pair =>
              obtain ⟨min, middle⟩ := pair
              obtain ⟨r, hu', hd'⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
              cases r with
              | Err e =>
                  simp [metadata.decode_limits, hr, hu, hu', hone, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    error.Error.Insts.CoreConvertFromOpError.from, ParserPost]
              | Ok pair =>
                  obtain ⟨max, next⟩ := pair
                  simp [metadata.decode_limits, hr, hu, hu', hone,
                    core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
                  obtain ⟨first, hs, hl, hb, he⟩ := hd
                  obtain ⟨rest, hs', hl', hb', he'⟩ := hd'
                  refine ⟨1#u8 :: (first ++ rest), by
                    simp only [LimitsEncoding, Source.bytes, List.map_cons, List.map_append]
                    exact .max min.val max.val ((Leb128.encoding_iff _ _).mp he) ((Leb128.encoding_iff _ _).mp he'), ?_⟩
                  simpa [hone] using (At.byte hp).append
                    ((show Body.Scalar.BytesAt data pos first middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)
        · simp [metadata.decode_limits, hr, core.result.Result.Insts.CoreOpsTry.branch, ParserPost]
          split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

/-- `metadata.decode_mem_type` returns a `MemTypeEncoding` span whose limits are within
`limits.MAX_MEMORY_PAGES`. -/
@[step]
theorem metadata.decode_mem_type.spec (data : Slice U8) (start : Usize) :
    metadata.decode_mem_type data start ⦃ r => match r with
      | .Ok (ty, next) => At MemTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_MEMORY_PAGES
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (metadata.decode_limits.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_mem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨lim, next⟩ := pair
      obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_MEMORY_PAGES)
      cases r with
      | Err e =>
          simp [metadata.decode_mem_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          simp [metadata.decode_mem_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hd, hp rfl⟩

namespace Binary

/-- A repetition span extends by one element at its end. -/
theorem At.rep_snoc {α : Type} {R : α → List U8 → Prop} {data start pos next xs x}
    (h : At (Rep R) data start xs pos) (h' : At R data pos x next) :
    At (Rep R) data start (xs ++ [x]) next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨last, he', hs'⟩ := h'
  exact ⟨bytes ++ last, he.snoc he', hs.append hs'⟩

end Binary

/-- The counted loop returns `count` value types forming a `Rep ValueTypeEncoding` span. -/
theorem metadata.decode_value_types_loop.spec (data : Slice U8) (start : Usize)
    (count : U32) (hb : start.val ≤ data.length) :
    metadata.decode_value_types_loop data count (alloc.vec.Vec.new wasm_types.ValueType) start 0#u32 ⦃ r =>
      match r with
      | .Ok (out, next) => At (Rep ValueTypeEncoding) data start out.val next ∧
          out.val.length = count.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_value_types_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      s.2.1.val = start.val + s.2.2.val ∧
      At (Rep ValueTypeEncoding) data start s.1.val s.2.1)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hpos, hrep⟩
    dsimp only at *
    by_cases hdone : count.val ≤ i.val
    · have he : i ≥ count := by scalar_tac
      simp [metadata.decode_value_types_loop.body, he]
      exact ⟨hrep, by omega⟩
    · have he : ¬i ≥ count := by scalar_tac
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (metadata.decode_value_type.syntax_spec data pos)
      cases r with
      | Err e =>
          simp [metadata.decode_value_types_loop.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨ty, next⟩ := pair
          obtain ⟨bytes, hbytes, hs⟩ := hd
          have hbts : bytes = [Itasca.Binary.valueByte ty] := ValueTypeEncoding.reader_bytes.mp hbytes
          subst bytes
          have hn : next.val = pos.val + 1 := by simpa using hs.length
          have hb' := hs.bound
          simp [metadata.decode_value_types_loop.body, he, hr,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac, ?_, by scalar_tac⟩
          · simp only [out1_post, List.length_append, List.length_singleton]
            scalar_tac
          · rw [out1_post]
            exact hrep.rep_snoc ⟨_, hbytes, hs⟩
  · exact ⟨by scalar_tac, rfl, by simp, ⟨[], .nil, Body.Scalar.BytesAt.nil data start hb⟩⟩

/-- `metadata.decode_value_types` returns a `VecEncoding ValueTypeEncoding` span within the length
bound. -/
theorem metadata.decode_value_types.spec (data : Slice U8) (start : Usize) (limit : Usize)
    (err : error.OpError) :
    metadata.decode_value_types data start limit err ⦃ r => match r with
      | .Ok (out, next) => At (VecEncoding ValueTypeEncoding) data start out.val next ∧
          out.val.length ≤ limit.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨count, pos⟩ := pair
      by_cases hbig : count.val > limit.val
      · simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, hbig]
      · obtain ⟨r, hv, hp⟩ := WP.spec_imp_exists
          (metadata.decode_value_types_loop.spec data pos count hd.span.2.2)
        have hrun : metadata.decode_value_types data start limit err =
            metadata.decode_value_types_loop data count (alloc.vec.Vec.new _) pos 0#u32 := by
          simp [metadata.decode_value_types, hr, core.result.Result.Insts.CoreOpsTry.branch, lift, hbig]
        rw [hrun, hv]
        cases r with
        | Err e => simp
        | Ok pair =>
            obtain ⟨out, next⟩ := pair
            obtain ⟨he, hlen⟩ := hp
            simp only [WP.spec_ok]
            constructor
            · obtain ⟨countBytes, hcs, hcl, hcb, hcount⟩ := hd
              obtain ⟨entries, hr, hs⟩ := he
              exact ⟨countBytes ++ entries,
                ⟨countBytes, entries, by simpa [hlen] using hcount, hr, rfl⟩,
                (show Body.Scalar.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩
            · have hc := U32.cast_Usize_val_eq count
              scalar_tac

/-- `metadata.decode_func_type` returns a `FuncTypeEncoding` span and satisfies the implementation
signature cap (`CodeEntry.FuncTypeWithinLimits`). -/
@[step]
theorem metadata.decode_func_type.spec (data : Slice U8) (start : Usize) :
    metadata.decode_func_type data start ⦃ r => match r with
      | .Ok (ty, next) => At FuncTypeEncoding data start ty next ∧
          CodeEntry.FuncTypeWithinLimits ty
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_func_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨tag, pos⟩ := pair
      by_cases he : tag = 0x60#u8
      · obtain ⟨r, hv, hd⟩ := WP.spec_imp_exists (metadata.decode_value_types.spec
          data pos limits.MAX_MULTI_VALUE_PARAMS error.OpError.TooManyParams)
        cases r with
        | Err e =>
            simp [metadata.decode_func_type, hr, he, hv, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
            obtain ⟨params, middle⟩ := pair
            obtain ⟨r, hv', hd'⟩ := WP.spec_imp_exists (metadata.decode_value_types.spec
              data middle limits.MAX_MULTI_VALUE_RESULTS error.OpError.TooManyResults)
            cases r with
            | Err e =>
                simp [metadata.decode_func_type, hr, he, hv, hv', core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
                obtain ⟨results, next⟩ := pair
                obtain ⟨paramsBytes, he1, hs1⟩ := hd.1
                obtain ⟨resultsBytes, he2, hs2⟩ := hd'.1
                have hat : At FuncTypeEncoding data start {params, results} next :=
                  ⟨0x60#u8 :: (paramsBytes ++ resultsBytes),
                    FuncTypeEncoding.reader_parts.mpr ⟨paramsBytes, resultsBytes, he1, he2, rfl⟩,
                    by simpa [he] using (At.byte hp).append (hs1.append hs2)⟩
                have hlimits : CodeEntry.FuncTypeWithinLimits {params, results} :=
                  ⟨hd.2, hd'.2⟩
                simp [metadata.decode_func_type, hr, he, hv, hv',
                  core.result.Result.Insts.CoreOpsTry.branch]
                exact ⟨hat, hlimits⟩
      · have hv : tag.val ≠ 96 := by
          intro h
          exact he (UScalar.eq_of_val_eq h)
        simp [metadata.decode_func_type, hr, hv, core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_global_type` returns a `GlobalTypeEncoding` span. -/
theorem metadata.decode_global_type.spec (data : Slice U8) (start : Usize) :
    metadata.decode_global_type data start ⦃ r => match r with
      | .Ok (ty, next) => At GlobalTypeEncoding data start ty next
      | .Err _ => True ⦄ := by
  obtain ⟨r, ht, hd⟩ := WP.spec_imp_exists (metadata.decode_value_type.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_global_type, ht, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨ty, pos⟩ := pair
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
      cases r with
      | Err e =>
          simp [metadata.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨mutability, next⟩ := pair
          obtain ⟨bytes, he, hs⟩ := hd
          have heq : bytes = [Itasca.Binary.valueByte ty] := ValueTypeEncoding.reader_bytes.mp he
          subst bytes
          by_cases hzero : mutability = 0#u8
          · simp [metadata.decode_global_type, ht, hr, hzero, core.result.Result.Insts.CoreOpsTry.branch]
            exact ⟨_, GlobalTypeEncoding.reader_bytes.mpr rfl, by simpa [hzero] using hs.append (At.byte hp)⟩
          · by_cases hone : mutability = 1#u8
            · simp [metadata.decode_global_type, ht, hr, hone, core.result.Result.Insts.CoreOpsTry.branch]
              exact ⟨_, GlobalTypeEncoding.reader_bytes.mpr rfl, by simpa [hone] using hs.append (At.byte hp)⟩
            · simp [metadata.decode_global_type, ht, hr, core.result.Result.Insts.CoreOpsTry.branch]
              split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

/-- `metadata.decode_table_type` returns its encoding and valid table limits. -/
theorem metadata.decode_table_type.spec (data : Slice U8) (start : Usize) :
    metadata.decode_table_type data start ⦃ r => match r with
      | .Ok (ty, next) => At TableTypeEncoding data start ty next ∧
          LimitsValid ty.limits limits.MAX_TABLE_ELEMS
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_elem_type.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_table_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨elem, pos⟩ := pair
      obtain ⟨r, hl, hd⟩ := WP.spec_imp_exists (metadata.decode_limits.spec data pos)
      cases r with
      | Err e =>
          simp [metadata.decode_table_type, hr, hl, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
          obtain ⟨lim, next⟩ := pair
          obtain ⟨r, hv, hvalid⟩ := WP.spec_imp_exists (limits.validate_limits.spec lim limits.MAX_TABLE_ELEMS)
          cases r with
          | Err e =>
              simp [metadata.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
              cases u
              have hrun : metadata.decode_table_type data start =
                  .ok (.Ok ({limits := lim, elem}, next)) := by
                simp [metadata.decode_table_type, hr, hl, hv, core.result.Result.Insts.CoreOpsTry.branch]
              rw [hrun]
              simp only [WP.spec_ok]
              obtain ⟨bytes, hc, hs⟩ := hd
              obtain ⟨eb, rfl, hes⟩ := hp
              refine ⟨⟨elemByte elem :: bytes, ⟨Source.bytes bytes, hc, by cases elem <;> rfl⟩, ?_⟩, hvalid rfl⟩
              exact hes.append hs

end Itasca

end

end

/-! ## Syntax -/

section

/-!
# Reader composition and UTF-8 syntax

Span inversion and completeness for primitive tags, headers, copies and lookups connect
independent bytes to actual reads. UTF-8 sequence contracts preserve exact names for the
name-reader layer.
-/

/-! ## BasicComplete -/

section

/-!
# Completeness of the primitive readers

Inversion lemmas for `At` over index, byte, repetition and vector encodings, and acceptance
(`.complete`) of `metadata.decode_value_type` and `metadata.decode_elem_type` from independent
encodings. The matching soundness specs are in `Module/Readers/Primitives`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- An `IndexEncoding` span is a decoded `u32`. -/
theorem At.index_decoded {data pos idx next} (h : At IndexEncoding data pos idx next) :
    Binary.Leb128.Decoded data pos idx next := by
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
    ∃ count middle, count.val = values.length ∧ Binary.Leb128.Decoded data pos count middle ∧
      At (Rep R) data middle values next := by
  obtain ⟨bytes, ⟨countBytes, entries, hc, he, rfl⟩, hs⟩ := h
  let count : U32 := U32.ofNatCore values.length (by have := hc.value_lt; scalar_tac)
  have hcount : count.val = values.length := by simp [count]
  obtain ⟨middle, hf, ht⟩ := hs.split
  exact ⟨count, middle, hcount, hf.u32_decoded count (by simpa [hcount] using hc), ⟨entries, he, ht⟩⟩

end Itasca.Binary

namespace Itasca

open Binary

/-- `metadata.decode_value_type` accepts an independently encoded value type. -/
theorem metadata.decode_value_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.ValueType) (next : Usize) (h : At ValueTypeEncoding data pos ty next) :
    metadata.decode_value_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, hb, hs⟩ := h
  obtain rfl := ValueTypeEncoding.reader_bytes.mp hb
  have hr := hs.read_byte
  cases ty <;>
    simp_all [metadata.decode_value_type, Itasca.Binary.valueByte, Itasca.Binary.Source.valueType, WebAssembly.Binary.valueByte, Itasca.Binary.Source.readerByte,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_elem_type` accepts an independently encoded element type. -/
theorem metadata.decode_elem_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.ElemType) (next : Usize) (h : At ElemTypeEncoding data pos ty next) :
    metadata.decode_elem_type data pos = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases ty <;>
    simp_all [metadata.decode_elem_type, elemByte, Body.ReferencesBinary.referenceByte, Translation.referenceType,
      WebAssembly.Binary.ReferencesBinary.referenceByte, Source.readerByte,
      core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## Header -/

section

/-!
# Module header reader

`metadata.read_header.spec`: an accepted header is the magic and version bytes at offset 0. The
completeness counterpart is in `Module/Readers/Syntax`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Binary

/-- An accepted result of `metadata.read_header` consumes exactly the magic and version bytes. -/
theorem metadata.read_header.spec (data : Slice U8) :
    metadata.read_header data ⦃ r => match r with
      | .Ok next => Body.Scalar.BytesAt data 0#usize magicVersion next
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
                                    simp only [magicVersion, List.cons.injEq, Source.readerByte]
                                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> apply UScalar.eq_of_val_eq <;> assumption
                                  simpa [heq] using hbytes

end Itasca

end

/-! ## FramingComplete -/

section

/-!
# Completeness of section framing

Acceptance (`.complete`) of `metadata.have_bytes`, `metadata.copy_bytes`, `metadata.read_section_header`
and `metadata.read_header` from independent byte spans, and `At.section_split`, which recovers the
header and payload spans of a complete section encoding. Soundness is in `Module/Readers/Primitives` and
`Module/Readers/Syntax`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A section encoding splits into a `SectionHeader` and the payload span. -/
theorem At.section_split {α : Type} {R : α → List U8 → Prop}
    {data pos next id value} (h : At (SectionEncoding id R) data pos value next) :
    ∃ first, SectionHeader data pos id first next ∧ At R data first value next := by
  obtain ⟨bytes, ⟨sizeBytes, payload, hsize, hvalue, rfl⟩, hs⟩ := h
  obtain ⟨middle, hid, hrest⟩ :=
    (show Body.Scalar.BytesAt data pos ([id] ++ (sizeBytes ++ payload)) next from hs).split
  obtain ⟨first, hcount, hbytes⟩ := hrest.split
  let count : U32 := U32.ofNatCore payload.length (by have := hsize.value_lt; scalar_tac)
  have hc : count.val = payload.length := by simp [count]
  exact ⟨first, ⟨middle, count, ⟨[id], rfl, hid⟩,
    hcount.u32_decoded count (by simpa [hc] using hsize),
    by simpa [hc] using hbytes.length, hbytes.bound⟩, ⟨payload, hvalue, hbytes⟩⟩

end Itasca.Binary

namespace Itasca
open Binary

/-- `metadata.have_bytes` accepts when the bytes are available. -/
theorem metadata.have_bytes.complete (data : Slice U8) (pos n : Usize)
    (h : pos.val + n.val ≤ data.length) : metadata.have_bytes data pos n = .ok (.Ok ()) := by
  obtain ⟨r, hr, hgood, _⟩ := WP.spec_imp_exists
    (metadata.have_bytes.spec data pos n (by omega))
  exact (hgood.mpr h) ▸ hr

/-- Copying a known byte interval recovers its exact vector, including empty intervals. -/
theorem metadata.copy_bytes.complete (data : Slice U8) (first last : Usize)
    (out : alloc.vec.Vec U8) (h : Body.Scalar.BytesAt data first out.val last) :
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
    (h : Body.Scalar.BytesAt data 0#usize magicVersion next) :
    metadata.read_header data = .ok (.Ok next) := by
  have hn : next = 8#usize := UScalar.eq_of_val_eq (by simpa [magicVersion] using h.length)
  subst next
  have hdata : data.val = magicVersion ++ data.val.drop 8 := by simpa using h.suffix
  generalize hrest : data.val.drop 8 = rest at hdata
  have h0 := read_at data 0#usize 1#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h4 := read_at data 4#usize 5#usize 1#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h5 := read_at data 5#usize 6#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h6 := read_at data 6#usize 7#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
  have h7 := read_at data 7#usize 8#usize 0#u8 (by simp [hdata, magicVersion]) rfl (by simp [hdata, magicVersion] <;> rfl)
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

end Itasca

end

/-! ## SegmentIndex -/

section

/-!
# Segment index decoder

Soundness (`spec`) and acceptance (`complete`) of `metadata.decode_segment_index`,
which reads the optional explicit table or memory index of an active segment according to
`SegmentIndexEncoding`.
-/

open Aeneas Aeneas.Std

namespace Itasca
open Binary

/-- `metadata.decode_segment_index` returns the index, next cursor and whether the index was
explicit, with the bytes consumed matching `SegmentIndexEncoding` for the flag word. -/
theorem metadata.decode_segment_index.spec (data : Slice U8) (pos : Usize)
    (flags : U32) (hpos : pos.val ≤ data.length) :
    metadata.decode_segment_index data pos flags ⦃ r => match r with
      | .Ok (idx, next, explicit) =>
          At (fun pair => SegmentIndexEncoding flags pair.1 pair.2)
            data pos (idx, explicit) next
      | .Err _ => True ⦄ := by
  by_cases hzero : flags = 0#u32
  · subst flags
    simp only [metadata.decode_segment_index]
    exact ⟨[], Or.inl ⟨rfl, rfl, rfl, rfl⟩, Body.Scalar.BytesAt.nil data pos hpos⟩
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
theorem metadata.decode_segment_index.complete {data : Slice U8} {pos next : Usize}
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
`Module/Readers/Completeness`.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 1200000

namespace Itasca.Binary

/-- The `count` bytes at `pos` are in range and form one canonical UTF-8 character. -/
def Utf8Sequence (bytes : Slice U8) (pos count : Usize) : Prop :=
  pos.val + count.val ≤ bytes.length ∧ 0 < count.val ∧
    Utf8Char ((bytes.val.drop pos.val).take count.val)

/-- UTF-8 validity is closed under concatenation. -/
theorem Utf8.append {first rest} (h : Utf8 first) (h' : Utf8 rest) : Utf8 (first ++ rest) := by
  induction h with
  | nil => simpa using h'
  | cons hc _ ih => simpa [List.append_assoc] using WebAssembly.Binary.Utf8With.cons hc ih

end Itasca.Binary

namespace Itasca

open Binary

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
    | (rw [take_one bytes.val pos.val (by scalar_tac)]; apply WebAssembly.Binary.Utf8CharWith.one; scalar_tac)
    | (rw [take_two bytes.val pos.val (by scalar_tac)]; apply WebAssembly.Binary.Utf8CharWith.two <;> scalar_tac)
    | (rw [take_three bytes.val pos.val (by scalar_tac)]; apply WebAssembly.Binary.Utf8CharWith.three <;> scalar_tac)
    | (rw [take_four bytes.val pos.val (by scalar_tac)]; apply WebAssembly.Binary.Utf8CharWith.four <;> scalar_tac)

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
          exact hprefix.append (by simpa using WebAssembly.Binary.Utf8With.cons hchar WebAssembly.Binary.Utf8With.nil)
  · exact ⟨by simp, by simpa using WebAssembly.Binary.Utf8With.nil⟩

end Itasca

end

end
