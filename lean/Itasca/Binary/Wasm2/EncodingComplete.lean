import Itasca.Binary.Wasm2.Encoding
import Itasca.Binary.Wasm2.SyntaxComplete
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Reading Wasm 2.0 encodings

Splitting lemmas for the Wasm 2.0 `At` and `Consumed` relations, as in
`Binary/Wasm1/EncodingComplete`. `At.read_op` splits a token into the opcode that
`code.read_op` returns and its immediate span.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A token interval is its opcode byte at the cursor followed by an immediate span. -/
theorem At.immediate {data start token next} (h : At data start token next)
    (pos : Usize) (hpos : pos.val = start.val + 1) :
    ∃ opcode immediate, Immediate opcode token immediate ∧
      (∃ hp : start.val < data.length, data.val[start.val] = opcode) ∧
      Wasm1.BytesAt data pos immediate next := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  have hl := hs.length
  have hb := hs.bound
  simp only [List.length_cons] at hl
  have hp : start.val < data.length := by omega
  have heq := hs.suffix
  rw [List.drop_eq_getElem_cons hp] at heq
  refine ⟨opcode, imm, hi, ⟨hp, (List.cons.inj heq).1⟩, ?_⟩
  exact ⟨by simpa [hpos] using (List.cons.inj heq).2, by omega, hb⟩

/-- `code.read_op` reads the opcode of a token and leaves the cursor at its immediate. -/
theorem At.read_op {data start token next} (h : At data start token next)
    (st : code.OpIterState) (hpos : st.pos = start) :
    ∃ opcode pos immediate,
      code.read_op st data = .ok (.Ok opcode, { st with pos := pos }) ∧
      pos.val = start.val + 1 ∧ Immediate opcode token immediate ∧
      Wasm1.BytesAt data pos immediate next := by
  have hp : st.pos.val < data.length := by
    have := h.span
    simpa [hpos] using Nat.lt_of_lt_of_le this.1 this.2
  obtain ⟨pos, hr, hn⟩ := code.read_op_success st data hp
  have hn' : pos.val = start.val + 1 := by simpa [hpos] using hn
  obtain ⟨opcode, imm, hi, ⟨_, hb⟩, hs⟩ := h.immediate pos hn'
  exact ⟨opcode, pos, imm, by simpa [hpos, hb] using hr, hn', hi, hs⟩

/-- A consumed span splits at any token boundary. -/
theorem Consumed.split_eq {data start tokens next} (h : Consumed data start tokens next)
    (first rest : List Token) (heq : tokens = first ++ rest) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next := by
  induction h generalizing first rest with
  | nil hb =>
      have hempty : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases hempty with ⟨rfl, rfl⟩
      exact ⟨start, .nil start hb, .nil start hb⟩
  | @snoc tokens pos token next hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = tokens ++ [token] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil next hlast.span.2⟩
      | append_singleton rest last =>
          have heq' : tokens ++ [token] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : token = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          have hp : tokens = first ++ rest := List.append_cancel_right heq'
          obtain ⟨middle, hf, hr⟩ := ih first rest hp
          exact ⟨middle, hf, .snoc hr hlast⟩

/-- A consumed span of a concatenation splits into consecutive spans. -/
theorem Consumed.split {data start next first rest}
    (h : Consumed data start (first ++ rest) next) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next :=
  h.split_eq first rest rfl

/-- An empty token list leaves the cursor in place. -/
theorem Consumed.empty_eq {data start tokens next}
    (h : Consumed data start tokens next) (he : tokens = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

/-- A consumed span of one token is an `At`. -/
theorem Consumed.single {data start next token}
    (h : Consumed data start [token] next) : At data start token next := by
  generalize he : [token] = tokens at h
  cases h with
  | nil => simp at he
  | @snoc tokens pos last next hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : tokens = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = token := by simpa [ht] using he.symm
      have hpos := hp.empty_eq ht
      simpa [heq, hpos] using hl

/-- A nonempty consumed span is its first token followed by the rest. -/
theorem Consumed.cons_iff {data start next token tokens} :
    Consumed data start (token :: tokens) next ↔
      ∃ middle, At data start token middle ∧ Consumed data middle tokens next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := h.split_eq [token] tokens rfl
    exact ⟨middle, hh.single, ht⟩
  · rintro ⟨middle, hh, ht⟩
    have hb : start.val ≤ data.length := by have := hh.span; omega
    exact Consumed.append (.snoc (.nil start hb) hh) ht


end Itasca.Wasm2
