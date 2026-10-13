import Itasca.Handler.Block
import Itasca.Handler.ControlFlow
import Itasca.Binary.Wasm1.EncodingComplete

open Aeneas Aeneas.Std

namespace Itasca

/-- Block-type decoding terminates on every byte sequence, including EOF and
the type-index encodings that are outside Wasm 1.0. -/
theorem code.read_block_type.raw_spec (data : Slice U8) (pos : Usize) :
    code.read_block_type data pos ⦃ r =>
      match r with
      | .Ok (bt, next) => Control.BlockDecoded data pos bt next
      | .Err e => e = .UnexpectedEof ∨ e = .InvalidBlockType ⦄ := by
  classical
  by_cases hp : pos.val < data.length
  · by_cases hb : ∃ bt, Control.ScalarBlockType bt ∧ data.val[pos.val] = Control.blockByte bt
    · obtain ⟨bt, hbt, hb⟩ := hb
      apply WP.spec_mono (code.read_block_type.spec data pos bt hp hb hbt)
      rintro _ ⟨next, rfl, hn⟩
      exact ⟨hp, hb, hn, by omega, hbt⟩
    · rw [code.read_block_type.invalid data pos hp (by simpa using hb)]
      simp
  · rw [code.read_block_type.eof data pos (by omega)]
    simp

theorem code.read_block.raw_spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_block st data ⦃ r =>
      ∀ bt, r.1 = .Ok bt → Control.BlockDecoded data st.pos bt r.2.pos ∧
        r.2.vals = st.vals ∧
        r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Block bt] ⦄ := by
  obtain ⟨res, hr, hout⟩ := WP.spec_imp_exists (code.read_block_type.raw_spec data st.pos)
  cases res with
  | Err e =>
      simp [code.read_block, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨bt, next⟩ := pair
      obtain ⟨hp, hb, hn, hbound, hbt⟩ := hout
      apply WP.spec_mono (code.read_block.spec st data bt hp hb hsize hbt)
      rintro r ⟨hok, hp', hv, hc⟩ b heq
      have : b = bt := by simpa [hok] using heq.symm
      subst b
      exact ⟨⟨hp, hb, hp', by omega, hbt⟩, hv, hc⟩

theorem code.read_loop.raw_spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_loop st data ⦃ r =>
      ∀ bt, r.1 = .Ok bt → Control.BlockDecoded data st.pos bt r.2.pos ∧
        r.2.vals = st.vals ∧
        r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Loop bt] ⦄ := by
  obtain ⟨res, hr, hout⟩ := WP.spec_imp_exists (code.read_block_type.raw_spec data st.pos)
  cases res with
  | Err e =>
      simp [code.read_loop, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨bt, next⟩ := pair
      obtain ⟨hp, hb, hn, hbound, hbt⟩ := hout
      apply WP.spec_mono (code.read_loop.spec st data bt hp hb hsize hbt)
      rintro r ⟨hok, hp', hv, hc⟩ b heq
      have : b = bt := by simpa [hok] using heq.symm
      subst b
      exact ⟨⟨hp, hb, hp', by omega, hbt⟩, hv, hc⟩

theorem code.read_if.raw_spec (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_if st data ⦃ r =>
      ∀ bt, r.1 = .Ok bt → Control.BlockDecoded data st.pos bt r.2.pos ∧
        ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
          r.2.ctrls.val = st.ctrls.val ++ [Control.frame r.2 .Then bt] ∧
          ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
            Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32]) ⦄ := by
  obtain ⟨res, hr, hout⟩ := WP.spec_imp_exists (code.read_block_type.raw_spec data st.pos)
  cases res with
  | Err e =>
      simp [code.read_if, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
      obtain ⟨bt, next⟩ := pair
      apply WP.spec_mono (code.read_if.from_block_type st data bt next outer segment
        hr hvals hbase hsize)
      rintro ⟨res, s⟩ ⟨hp, hs⟩ b heq
      dsimp only at heq hp hs ⊢
      subst res
      obtain ⟨rfl, hs⟩ := hs
      exact ⟨by simpa [hp] using hout, hs⟩

end Itasca

namespace Itasca.Wasm1

theorem BytesAt.read_block_type {data start next} (bt : code.BlockType)
    (h : BytesAt data start [Control.blockByte bt] next)
    (hbt : Control.ScalarBlockType bt) :
    code.read_block_type data start = .ok (.Ok (bt, next)) := by
  obtain ⟨hp, hb, hn⟩ := h.single
  obtain ⟨_, hr, p, rfl, hp'⟩ := WP.spec_imp_exists (code.read_block_type.spec data start bt hp hb hbt)
  have heq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [heq] using hr

theorem At.read_block {data start next} (bt : code.BlockType)
    (h : At data start (.block bt) next) (pos : Usize) (hp : pos.val = start.val + 1) :
    code.read_block_type data pos = .ok (.Ok (bt, next)) := by
  obtain ⟨opcode, imm, hi, _, hs⟩ := h.immediate pos hp
  cases hi
  exact hs.read_block_type bt (by assumption)

theorem At.read_loop {data start next} (bt : code.BlockType)
    (h : At data start (.loop bt) next) (pos : Usize) (hp : pos.val = start.val + 1) :
    code.read_block_type data pos = .ok (.Ok (bt, next)) := by
  obtain ⟨opcode, imm, hi, _, hs⟩ := h.immediate pos hp
  cases hi
  exact hs.read_block_type bt (by assumption)

theorem At.read_if {data start next} (bt : code.BlockType)
    (h : At data start (.if_ bt) next) (pos : Usize) (hp : pos.val = start.val + 1) :
    code.read_block_type data pos = .ok (.Ok (bt, next)) := by
  obtain ⟨opcode, imm, hi, _, hs⟩ := h.immediate pos hp
  cases hi
  exact hs.read_block_type bt (by assumption)

end Itasca.Wasm1
