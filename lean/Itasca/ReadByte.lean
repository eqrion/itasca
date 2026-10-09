import Itasca.ScalarMatch

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace Itasca

/-- Reading within a slice returns its byte and advances the cursor exactly once. -/
@[step]
theorem reader.read_byte.spec (data : Slice U8) (pos : Usize)
    (h : pos.val < data.length) :
    reader.read_byte data pos ⦃ (r : core.result.Result (U8 × Usize) error.OpError) =>
      ∃ next, r = .Ok (data.val[pos.val], next) ∧ next.val = pos.val + 1 ⦄ := by
  unfold reader.read_byte
  step*
  exact ⟨i1, by rw [b_post], i1_post⟩

/-- End-of-input is an ordinary validation error, not a modeled panic. -/
theorem reader.read_byte.eof (data : Slice U8) (pos : Usize)
    (h : data.length ≤ pos.val) :
    reader.read_byte data pos = .ok (.Err .UnexpectedEof) := by
  unfold reader.read_byte
  have hb : pos ≥ Slice.len data := by scalar_tac
  simp only [hb, ↓reduceIte]

/-- Opcode decoding changes only the cursor and returns the byte at that cursor. -/
theorem code.read_op_success (st : code.OpIterState) (data : Slice U8)
    (h : st.pos.val < data.length) :
    ∃ next, code.read_op st data =
      .ok (.Ok (data.val[st.pos.val]), { st with pos := next }) ∧
      next.val = st.pos.val + 1 := by
  obtain ⟨r, hr, next, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos h)
  refine ⟨next, ?_, hnext⟩
  rw [code.read_op, hr]
  simp [core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
