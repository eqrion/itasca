import Itasca.Binary.UnicodeUnique
import Itasca.Profile.Types

/-!
Sections, each formerly its own module: Basic, Types.
-/

/-! ## Basic -/

section

/-!
# Primitive module readers

Soundness specs for the byte-level helpers of the module parser: `reader.read_byte`,
`metadata.have_bytes`, `metadata.copy_bytes`, `metadata.read_section_header`, `limits.validate_limits`,
`metadata.decode_value_type` and `metadata.decode_elem_type`. Each relates a successful result to the
independent grammar through `ParserPost`, or states `SectionHeader` and `LimitsValid`. Completeness
is in `Module/Readers/BasicComplete` and `Module/Readers/FramingComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A parser result is either an error, or a value and next cursor with `At R data start value
next`. It carries no guarantee for errors. -/
def ParserPost {α : Type} (R : α → List U8 → Prop) (data : Slice U8) (start : Usize) :
    core.result.Result (α × Usize) error.Error → Prop
  | .Ok (value, next) => At R data start value next
  | .Err _ => True

/-- A decoded `u32` is an `IndexEncoding`. -/
theorem At.of_u32 {data start value next} (h : Leb128.Decoded data start value next) :
    At IndexEncoding data start value next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := h
  exact ⟨bytes, he, hs, hl, hb⟩

/-- A one-byte encoding covers exactly that byte. -/
theorem At.byte {data start byte next}
    (h : At ByteEncoding data start byte next) : Wasm1.BytesAt data start [byte] next := by
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

/-- A section header at `start` with id `id` and a `u32` size. The payload runs from `first` to
`last` and lies entirely within `data`. -/
def SectionHeader (data : Slice U8) (start : Usize) (id : U8) (first last : Usize) : Prop :=
  ∃ pos size, At ByteEncoding data start id pos ∧ Leb128.Decoded data pos size first ∧
    last.val = first.val + size.val ∧ last.val ≤ data.length

/-- The payload interval of a header is ordered and within the input. -/
theorem SectionHeader.span {data start id first last}
    (h : SectionHeader data start id first last) :
    start.val < first.val ∧ first.val ≤ last.val ∧ last.val ≤ data.length := by
  obtain ⟨pos, size, hb, hd, hn, he⟩ := h
  have hs := hb.byte.length
  have hi := hd.span
  simp only [List.length_singleton] at hs
  omega

end Itasca.ModuleBinary

namespace Itasca

/-- `reader.read_byte` returns normally, and a byte read is a `ByteEncoding` span; reading at EOF
is an error. -/
theorem reader.read_byte.module_spec (data : Slice U8) (pos : Usize) :
    reader.read_byte data pos ⦃ r => match r with
      | .Ok (value, next) => ModuleBinary.At ModuleBinary.ByteEncoding data pos value next
      | .Err _ => True ⦄ := by
  by_cases hb : pos.val < data.length
  · apply WP.spec_mono (reader.read_byte.spec data pos hb)
    rintro r ⟨next, rfl, hn⟩
    exact ⟨_, rfl, Wasm1.BytesAt.byte data pos next _ hb rfl hn⟩
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
      ModuleBinary.ParserPost ModuleBinary.ValueTypeEncoding data pos r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
  cases r with
  | Err e =>
      simp [metadata.decode_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, ModuleBinary.ParserPost]
  | Ok pair =>
      obtain ⟨b, next⟩ := pair
      have hs := ModuleBinary.At.byte hp
      simp [metadata.decode_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        ModuleBinary.ParserPost]
      all_goals split
      all_goals first
        | exact ⟨_, rfl, by with_unfolding_all exact hs⟩
        | simp

/-- `metadata.decode_elem_type` returns an element type with its exact encoding. -/
@[step]
theorem metadata.decode_elem_type.spec (data : Slice U8) (pos : Usize) :
    metadata.decode_elem_type data pos ⦃ r =>
      ModuleBinary.ParserPost ModuleBinary.ElemTypeEncoding data pos r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
  cases r with
  | Err e =>
      simp [metadata.decode_elem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from, ModuleBinary.ParserPost]
  | Ok pair =>
      obtain ⟨b, next⟩ := pair
      have hs := ModuleBinary.At.byte hp
      simp [metadata.decode_elem_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        ModuleBinary.ParserPost]
      all_goals split
      all_goals first
        | exact ⟨_, rfl, by with_unfolding_all exact hs⟩
        | simp

/-- `metadata.decode_value_type` returns a value type with its exact encoding. -/
theorem metadata.decode_value_type.syntax_spec (data : Slice U8) (pos : Usize) :
    metadata.decode_value_type data pos ⦃ r =>
      ModuleBinary.ParserPost ModuleBinary.ValueTypeEncoding data pos r ⦄ :=
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
    metadata.copy_bytes data first last ⦃ out => Wasm1.BytesAt data first out.val last ⦄ := by
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
    limits.validate_limits lim bound ⦃ r => r = .Ok () → ModuleBinary.LimitsValid lim bound ⦄ := by
  unfold limits.validate_limits ModuleBinary.LimitsValid
  step*
  simp_all

/-- `metadata.read_section_header` returns a `SectionHeader` for the bytes it consumed. -/
theorem metadata.read_section_header.spec (data : Slice U8) (start : Usize) :
    metadata.read_section_header data start ⦃ r => match r with
      | .Ok (id, first, last) => ModuleBinary.SectionHeader data start id first last
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
Completeness is in `Module/Readers/TypesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

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
            refine ⟨0#u8 :: bytes, .noMax min he, ?_⟩
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
                  refine ⟨1#u8 :: (first ++ rest), .max min max he he', ?_⟩
                  simpa [hone] using (At.byte hp).append
                    ((show Wasm1.BytesAt data pos first middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)
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

namespace ModuleBinary

/-- A repetition span extends by one element at its end. -/
theorem At.rep_snoc {α : Type} {R : α → List U8 → Prop} {data start pos next xs x}
    (h : At (Rep R) data start xs pos) (h' : At R data pos x next) :
    At (Rep R) data start (xs ++ [x]) next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨last, he', hs'⟩ := h'
  exact ⟨bytes ++ last, he.snoc he', hs.append hs'⟩

end ModuleBinary

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
          have hbts : bytes = [valueByte ty] := hbytes
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
            exact hrep.rep_snoc ⟨_, rfl, hs⟩
  · exact ⟨by scalar_tac, rfl, by simp, ⟨[], .nil, Wasm1.BytesAt.nil data start hb⟩⟩

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
                (show Wasm1.BytesAt data start countBytes pos from ⟨hcs, hcl, hcb⟩).append hs⟩
            · have hc := U32.cast_Usize_val_eq count
              scalar_tac

/-- `metadata.decode_func_type` returns a `FuncTypeEncoding` span and satisfies the implementation
signature cap (`Profile.FuncTypeWithinLimits`). -/
@[step]
theorem metadata.decode_func_type.profile_spec (data : Slice U8) (start : Usize) :
    metadata.decode_func_type data start ⦃ r => match r with
      | .Ok (ty, next) => At FuncTypeEncoding data start ty next ∧
          Profile.FuncTypeWithinLimits ty
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
                    ⟨paramsBytes, resultsBytes, he1, he2, rfl⟩,
                    by simpa [he] using (At.byte hp).append (hs1.append hs2)⟩
                have hlimits : Profile.FuncTypeWithinLimits {params, results} :=
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
          have heq : bytes = [valueByte ty] := he
          subst bytes
          by_cases hzero : mutability = 0#u8
          · simp [metadata.decode_global_type, ht, hr, hzero, core.result.Result.Insts.CoreOpsTry.branch]
            exact ⟨_, rfl, by simpa [hzero, mutByte] using hs.append (At.byte hp)⟩
          · by_cases hone : mutability = 1#u8
            · simp [metadata.decode_global_type, ht, hr, hone, core.result.Result.Insts.CoreOpsTry.branch]
              exact ⟨_, rfl, by simpa [hone, mutByte] using hs.append (At.byte hp)⟩
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
              refine ⟨⟨elemByte elem :: bytes, ⟨bytes, hc, rfl⟩, ?_⟩, hvalid rfl⟩
              exact hes.append hs

end Itasca

end
