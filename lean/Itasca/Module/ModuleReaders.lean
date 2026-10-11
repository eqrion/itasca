import Itasca.Binary.ModuleBinary

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

def ParserPost {α : Type} (R : α → List U8 → Prop) (data : Slice U8) (start : Usize) :
    core.result.Result (α × Usize) error.Error → Prop
  | .Ok (value, next) => At R data start value next
  | .Err _ => True

theorem At.of_u32 {data start value next} (h : Leb128.Decoded data start value next) :
    At IndexEncoding data start value next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := h
  exact ⟨bytes, he, hs, hl, hb⟩

theorem At.byte {data start byte next}
    (h : At ByteEncoding data start byte next) : Wasm.BytesAt data start [byte] next := by
  obtain ⟨bytes, rfl, hs⟩ := h
  exact hs

theorem At.prepend {α : Type} {R S : α → List U8 → Prop} {data start pos next b value}
    (hb : At ByteEncoding data start b pos) (hr : At R data pos value next)
    (hR : ∀ bytes, R value bytes → S value (b :: bytes)) : At S data start value next := by
  obtain ⟨bytes, he, hs⟩ := hr
  exact ⟨b :: bytes, hR bytes he, by simpa using hb.byte.append hs⟩

def LimitsValid (lim : types.Limits) (bound : U32) : Prop :=
  lim.min.val ≤ bound.val ∧ ∀ maximum, lim.max = some maximum →
    lim.min.val ≤ maximum.val ∧ maximum.val ≤ bound.val

/-- Header provenance, including the entire payload's availability. -/
def SectionHeader (data : Slice U8) (start : Usize) (id : U8) (first last : Usize) : Prop :=
  ∃ pos size, At ByteEncoding data start id pos ∧ Leb128.Decoded data pos size first ∧
    last.val = first.val + size.val ∧ last.val ≤ data.length

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

/-- Total byte reading, including EOF, in a form convenient for module parsers. -/
theorem reader.read_byte.module_spec (data : Slice U8) (pos : Usize) :
    reader.read_byte data pos ⦃ r => match r with
      | .Ok (value, next) => ModuleBinary.At ModuleBinary.ByteEncoding data pos value next
      | .Err _ => True ⦄ := by
  by_cases hb : pos.val < data.length
  · apply WP.spec_mono (reader.read_byte.spec data pos hb)
    rintro r ⟨next, rfl, hn⟩
    exact ⟨_, rfl, Wasm.BytesAt.byte data pos next _ hb rfl hn⟩
  · simp [reader.read_byte.eof data pos (by omega)]

/-- The subtraction-based bounds check terminates for an in-bounds cursor. -/
@[step]
theorem module.have_bytes.spec (data : Slice U8) (pos n : Usize)
    (hb : pos.val ≤ data.length) :
    module.have_bytes data pos n ⦃ r =>
      (r = .Ok () ↔ pos.val + n.val ≤ data.length) ∧
      (r = .Err .UnexpectedEof ↔ data.length < pos.val + n.val) ⦄ := by
  unfold module.have_bytes
  step* <;> scalar_tac

@[step]
theorem module.decode_value_type.spec (data : Slice U8) (pos : Usize) :
    module.decode_value_type data pos ⦃ r => ModuleBinary.ParserPost ModuleBinary.ValueTypeEncoding data pos r ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data pos)
  cases r with
  | Err e =>
      simp [module.decode_value_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from,
        ModuleBinary.ParserPost]
  | Ok pair =>
      obtain ⟨b, next⟩ := pair
      have hs := ModuleBinary.At.byte hp
      simp [module.decode_value_type, hr,
        core.result.Result.Insts.CoreOpsTry.branch, ModuleBinary.ParserPost]
      split
      · simp only [WP.spec_ok]
        exact ⟨_, rfl, by with_unfolding_all exact hs⟩
      · simp only [WP.spec_ok]
        exact ⟨_, rfl, by with_unfolding_all exact hs⟩
      · simp only [WP.spec_ok]
        exact ⟨_, rfl, by with_unfolding_all exact hs⟩
      · simp only [WP.spec_ok]
        exact ⟨_, rfl, by with_unfolding_all exact hs⟩
      · simp

private theorem copy_bytes_body (data : Slice U8) (last : Usize) (out : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val < last.val) (hb : last.val ≤ data.length)
    (hlen : out.val.length ≤ i.val) :
    module.copy_bytes_loop.body data last out i ⦃ r =>
      ∃ out' next, r = .cont (out', next) ∧
        out'.val = out.val ++ [data.val[i.val]'(by simpa using Nat.lt_of_lt_of_le hi hb)] ∧ next.val = i.val + 1 ⦄ := by
  unfold module.copy_bytes_loop.body
  step*
  exact ⟨out1, i2, rfl, by simpa [i1_post] using out1_post, i2_post⟩

/-- Copying a bounded range terminates and returns exactly that byte interval. -/
@[step]
theorem module.copy_bytes.spec (data : Slice U8) (first last : Usize)
    (hf : first.val ≤ last.val) (hb : last.val ≤ data.length) :
    module.copy_bytes data first last ⦃ out => Wasm.BytesAt data first out.val last ⦄ := by
  unfold module.copy_bytes module.copy_bytes_loop
  apply loop.spec_decr_nat (fun s => last.val - s.2.val)
    (fun s => first.val ≤ s.2.val ∧ s.2.val ≤ last.val ∧
      s.2.val = first.val + s.1.val.length ∧
      data.val.drop first.val = s.1.val ++ data.val.drop s.2.val)
  · rintro ⟨out, i⟩ ⟨hfirst, hlast, hlen, hs⟩
    dsimp only at *
    by_cases hdone : last.val ≤ i.val
    · have heq : i = last := UScalar.eq_of_val_eq (by omega)
      simp only [module.copy_bytes_loop.body, heq, ge_iff_le, le_refl, ↓reduceIte, WP.spec_ok]
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

@[step]
theorem limits.validate_limits.spec (lim : types.Limits) (bound : U32) :
    limits.validate_limits lim bound ⦃ r => r = .Ok () → ModuleBinary.LimitsValid lim bound ⦄ := by
  unfold limits.validate_limits ModuleBinary.LimitsValid
  step*
  simp_all

theorem module.read_section_header.spec (data : Slice U8) (start : Usize) :
    module.read_section_header data start ⦃ r => match r with
      | .Ok (id, first, last) => ModuleBinary.SectionHeader data start id first last
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data start)
  cases r with
  | Err e =>
      simp [module.read_section_header, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨id, pos⟩ := pair
      obtain ⟨r, hu, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      cases r with
      | Err e =>
          simp [module.read_section_header, hr, hu, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨size, first⟩ := pair
          have hspan := hd.span
          simp [module.read_section_header, hr, hu,
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

@[simp]
theorem module.decode_segment_index.wasm1 (data : Slice U8) (pos : Usize) (idx : U32) :
    module.decode_segment_index data pos idx .Wasm1 = .ok (.Ok (idx, pos, false)) := rfl

end Itasca
