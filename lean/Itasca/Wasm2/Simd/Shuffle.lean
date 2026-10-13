import Itasca.Wasm2.Simd.Decode
import Itasca.Wasm2.Simd.MemoryReaders
import Itasca.Binary.Wasm2.SimdBitsMeaning

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Simd

/-- Operand validation after the sixteen shuffle bytes have been range checked. -/
def shuffleFinish (st : code.OpIterState) (data : Slice U8) :
    Result (core.result.Result (U64 × U64) error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_simd_bits st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok bits => carryFixed bits s [.V128, .V128] (some .V128)

private theorem finish_body (st : code.OpIterState) (data : Slice U8) (pos : Usize) (i : I32)
    (hi : ¬ i < 16#i32) :
    code.read_simd_shuffle_loop.body st.vals st.ctrls st.pos data pos i = (do
      let r ← shuffleFinish st data
      .ok (.done r)) := by
  simp only [code.read_simd_shuffle_loop.body, hi, if_false, shuffleFinish, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok bits =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, binary_fixed, carryFixed,
      Std.bind_assoc, Std.uncurry]
    congr 1
    funext pair
    obtain ⟨r, s⟩ := pair
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The scanner reaches its operand reader only after checking all sixteen bytes. -/
theorem shuffle_scan (st : code.OpIterState) (data : Slice U8)
    (hpos : st.pos.val ≤ data.length)
    (Q : core.result.Result (U64 × U64) error.OpError × code.OpIterState → Prop)
    (herr : ∀ e, Q (.Err e, st))
    (hfinish : ∀ bytes next, Wasm.BytesAt data st.pos bytes next → bytes.length = 16 →
      (∀ b ∈ bytes, b.val < 32) → shuffleFinish st data ⦃ Q ⦄) :
    code.read_simd_shuffle st data ⦃ Q ⦄ := by
  unfold code.read_simd_shuffle code.read_simd_shuffle_loop
  apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
    (fun p => 0 ≤ p.2.val ∧ p.2.val ≤ 16 ∧ ∃ before : List U8,
      Wasm.BytesAt data st.pos before p.1 ∧ before.length = p.2.val.toNat ∧
      ∀ b ∈ before, b.val < 32)
  · rintro ⟨pos, i⟩ ⟨hi, hn, before, hb, hl, hbefore⟩
    dsimp only at *
    by_cases hlt : i < 16#i32
    · simp only [code.read_simd_shuffle_loop.body, hlt, if_true]
      by_cases hp : pos.val < data.length
      · obtain ⟨_, hr, next, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
        simp only [hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Std.uncurry]
        split
        · simpa using herr error.OpError.InvalidLane
        · rename_i hsmall
          step
          refine ⟨by scalar_tac, by scalar_tac, ⟨before ++ [data.val[pos.val]],
            hb.append (Wasm.BytesAt.byte data pos next _ hp rfl hnext), ?_, ?_⟩, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            scalar_tac
          · intro b hm
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact hbefore b hm
            · scalar_tac
          · scalar_tac
      · simp [reader.read_byte.eof data pos (by omega),
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, herr]
    · rw [finish_body st data pos i hlt]
      apply WP.spec_mono (WP.spec_bind (hfinish before pos hb (by scalar_tac) hbefore) ?_)
      · intro r hr; exact hr
      · intro r hr
        simpa using hr
  · dsimp only
    exact ⟨by decide, by decide, [], Wasm.BytesAt.nil data st.pos hpos, by simp, by simp⟩

/-- Every independently valid shuffle immediate reaches the operand reader. -/
theorem shuffle_complete (st : code.OpIterState) (data : Slice U8)
    (bytes : List U8) (next : Usize) (hb : Wasm.BytesAt data st.pos bytes next)
    (hl : bytes.length = 16) (hbound : ∀ b ∈ bytes, b.val < 32)
    (r : core.result.Result (U64 × U64) error.OpError × code.OpIterState)
    (hfinish : shuffleFinish st data = .ok r) :
    code.read_simd_shuffle st data = .ok r := by
  have hrun : code.read_simd_shuffle st data ⦃ result => result = r ⦄ := by
    unfold code.read_simd_shuffle code.read_simd_shuffle_loop
    apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
      (fun p => 0 ≤ p.2.val ∧ ∃ rest : List U8,
        Wasm.BytesAt data p.1 rest next ∧ p.2.val + (rest.length : Int) = 16 ∧
        ∀ b ∈ rest, b.val < 32)
    · rintro ⟨pos, i⟩ ⟨hi, rest, hrest, hlen, hsmall⟩
      dsimp only at *
      by_cases hlt : i < 16#i32
      · cases rest with
        | nil => simp only [List.length_nil] at hlen; scalar_tac
        | cons b rest =>
          obtain ⟨middle, hb1, hb2⟩ := (show Wasm.BytesAt data pos ([b] ++ rest) next from hrest).split
          have hblt : ¬ b ≥ 32#u8 := by have := hsmall b (by simp); scalar_tac
          simp only [code.read_simd_shuffle_loop.body, hlt, if_true, hb1.read_byte,
            bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Std.uncurry, hblt, if_false]
          step
          refine ⟨by scalar_tac, ⟨rest, hb2, ?_, fun b hb => hsmall b (by simp [hb])⟩, ?_⟩
          · simp only [List.length_cons] at hlen
            scalar_tac
          · simp only [List.length_cons] at hlen
            scalar_tac
      · rw [finish_body st data pos i hlt, hfinish]
        simp
    · dsimp only
      exact ⟨by decide, bytes, hb, by simpa [hl], hbound⟩
  obtain ⟨result, he, rfl⟩ := WP.spec_imp_exists hrun
  exact he

/-- The scanner's accepted words encode exactly the bounded lane vector and its stack effect. -/
theorem shuffle_segment (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (hv : st.vals.val = outer ++ segment)
    (hb : (Control.base st).val = outer.length) (hsize : st.vals.val.length < Usize.max)
    (hpos : st.pos.val ≤ data.length) :
    code.read_simd_shuffle st data ⦃ r => ∀ low high, r.1 = .Ok (low, high) →
      r.2.ctrls = st.ctrls ∧ ∃ after, r.2.vals.val = outer ++ after ∧
        BitsDecoded data st.pos low high r.2.pos ∧
        (∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32) ∧
        FixedEffect (Control.polymorphic st) segment [.V128, .V128] (some .V128) after ⦄ := by
  apply shuffle_scan st data hpos
  · intro e; simp
  · intro bytes next hbytes hlen hbounds
    obtain ⟨⟨r, decoded⟩, hd, hc, hvals, hbits⟩ := WP.spec_imp_exists (take_bits_spec st data)
    dsimp only at hc hvals hbits
    simp only [shuffleFinish, hd, bind_ok, Std.uncurry]
    cases r with
    | Err e => simp
    | Ok bits =>
      obtain ⟨low, high⟩ := bits
      have hdecoded := hbits low high rfl
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hdecoded
      have he : decoded.pos = next := by
        apply UScalar.eq_of_val_eq
        have h1 := hspan.length
        have h2 := hbytes.length
        simp only [List.length_append, hlo.1, hhi.1] at h1
        omega
      have hbytesEq : lower ++ upper = bytes := by
        have h1 := hspan.suffix
        rw [he, hbytes.suffix] at h1
        exact (List.append_cancel_right h1).symm
      have hbounded : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
        rw [shuffleIndices_encoding low high lower upper hlo hhi, hbytesEq]
        intro lane hm
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
        exact hbounds b hb
      apply WP.spec_mono (carryFixed.segment (low, high) decoded [.V128, .V128] (some .V128)
        outer segment (by simpa [hvals] using hv) (by simpa [Control.base, hc] using hb)
        (by simpa [hvals] using hsize))
      rintro ⟨res, s⟩ ⟨hctrl, hposition, after, hstack, _, heffect⟩ lo hi hok
      dsimp only at hctrl hposition hstack heffect hok
      obtain ⟨heq, heff⟩ := heffect (lo, hi) hok
      cases heq
      refine ⟨hctrl.trans hc, after, hstack, ?_, hbounded, ?_⟩
      · simpa only [hposition] using hbits low high rfl
      · simpa only [Control.polymorphic, hc] using heff

end Itasca.MultiValue.Simd
