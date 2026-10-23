import Itasca.Binary.Wasm1.Subset
import Itasca.Binary.Wasm2.EncodingComplete

/-!
# Profile-indexed token runs

Every Wasm 1.0 token is a Wasm 2.0 token (`Wasm1.At.to_wasm2`) whose opcode is outside the Wasm 2.0
extensions (`Wasm1.Immediate.not_extension`). `ProfileConsumed` is the token run of a profile's
grammar, so completeness proofs can split one run for either profile.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

theorem Immediate.to_wasm2 {opcode : U8} {token : Token} {bytes : List U8}
    (h : Immediate opcode token bytes) : Wasm2.Immediate opcode token bytes := by
  cases token with
  | plain op => exact .plain h
  | block bt => cases h with | block hb => exact .block (by cases hb <;> rfl)
  | loop bt => cases h with | loop hb => exact .loop (by cases hb <;> rfl)
  | if_ bt => cases h with | if_ hb => exact .if_ (by cases hb <;> rfl)
  | else_ => cases h; exact .else_
  | end_ => cases h; exact .end_

theorem Immediate.not_extension {opcode : U8} {token : Token} {bytes : List U8}
    (h : Immediate opcode token bytes) : opcode.val ∉ extensionOpcodes := by
  cases h with
  | memory _ _ _ meaning =>
    unfold MemoryMeaning.opcodeMeaning at meaning
    split at meaning <;> simp_all [extensionOpcodes]
  | numeric _ _ meaning =>
    have hb := Numeric.NumericOp.bounds meaning
    simp only [extensionOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | _ => decide

theorem At.to_wasm2 {data start token next} (h : At data start token next) :
    Wasm2.At data start token next := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  exact ⟨_, ⟨opcode, imm, rfl, hi.to_wasm2⟩, hs⟩

theorem Consumed.to_wasm2 {data start tokens next} (h : Consumed data start tokens next) :
    Wasm2.Consumed data start tokens next := by
  induction h with
  | nil bound => exact .nil _ bound
  | snoc _ hat ih => exact .snoc ih hat.to_wasm2

end Itasca.Wasm1

namespace Itasca

/-- The tokens read from `start` to `next` in the profile's binary grammar. -/
def ProfileConsumed : ValidationProfile → Slice U8 → Usize → List Wasm2.Token → Usize → Prop
  | .Wasm1 => Wasm1.Consumed
  | .Wasm2 => Wasm2.Consumed

namespace ProfileConsumed

theorem to_wasm2 {profile data start tokens next}
    (h : ProfileConsumed profile data start tokens next) : Wasm2.Consumed data start tokens next := by
  cases profile
  · exact Wasm1.Consumed.to_wasm2 h
  · exact h

theorem split {profile data start next first rest}
    (h : ProfileConsumed profile data start (first ++ rest) next) :
    ∃ middle, ProfileConsumed profile data start first middle ∧
      ProfileConsumed profile data middle rest next := by
  cases profile
  · exact Wasm1.Consumed.split h
  · exact Wasm2.Consumed.split h

theorem empty_eq {profile data start tokens next}
    (h : ProfileConsumed profile data start tokens next) (he : tokens = []) : next = start := by
  cases profile
  · exact Wasm1.Consumed.empty_eq h he
  · exact Wasm2.Consumed.empty_eq h he

theorem single {profile data start next token}
    (h : ProfileConsumed profile data start [token] next) :
    Wasm2.At data start token next ∧ (profile = .Wasm1 → Wasm1.At data start token next) := by
  cases profile
  · exact ⟨(Wasm1.Consumed.single h).to_wasm2, fun _ => Wasm1.Consumed.single h⟩
  · exact ⟨Wasm2.Consumed.single h, fun h => nomatch h⟩

end ProfileConsumed

end Itasca

namespace Itasca.Wasm1

/-- A Wasm 1.0 token read at a known opcode byte and immediate span has that opcode and
immediate. -/
theorem At.immediate_at {data start token next opcode pos imm} (h : At data start token next)
    (hp : start.val < data.length) (hb : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (hs : BytesAt data pos imm next) :
    Immediate opcode token imm := by
  obtain ⟨_, ⟨op1, imm1, rfl, hi⟩, hs1⟩ := h
  have h1 := hs1.suffix
  have h2 := hs.suffix
  rw [List.drop_eq_getElem_cons hp, hb] at h1
  have hd : data.val.drop (start.val + 1) = data.val.drop pos.val := by rw [hpos]
  rw [hd, h2] at h1
  simp only [List.cons_append, List.cons.injEq] at h1
  obtain ⟨rfl, h3⟩ := h1
  rw [List.append_cancel_right h3.symm] at hi
  exact hi

end Itasca.Wasm1

namespace Itasca.Wasm1

/-- Wasm 1.0 structured instruction headers have one-byte block types. -/
theorem At.blockTokenOk {data start token next} (h : At data start token next) :
    BlockTokenOk token := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, _⟩ := h
  cases hi <;> first | trivial | exact ⟨_, by assumption⟩

end Itasca.Wasm1

namespace Itasca.Wasm1

theorem BodyEncoding.to_wasm2 {data ops} (h : BodyEncoding data ops) : Wasm2.BodyEncoding data ops :=
  let ⟨tokens, next, hc, hn, hb⟩ := h
  ⟨tokens, next, hc.to_wasm2, hn, hb⟩

end Itasca.Wasm1
