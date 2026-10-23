import Itasca.Support.LiteralDispatch

/-!
# Single-byte reads

Specifications of the extracted `reader.read_byte` and of `code.read_op`, which reads one
opcode byte. Both return the byte at the cursor and advance it by one, or return
`UnexpectedEof` at the end of the input. These are the base case for the LEB128 and
instruction-level reader lemmas.
-/

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

/-- Reading at or past the end of the slice returns the `UnexpectedEof` validation error. -/
theorem reader.read_byte.eof (data : Slice U8) (pos : Usize)
    (h : data.length ≤ pos.val) :
    reader.read_byte data pos = .ok (.Err .UnexpectedEof) := by
  unfold reader.read_byte
  have hb : pos ≥ Slice.len data := by scalar_tac
  simp only [hb, ↓reduceIte]

end Itasca
