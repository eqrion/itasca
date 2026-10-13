import Itasca.Binary.Wasm2.Syntax

namespace Itasca.MultiValue

/-- A single generated instruction and its complete flat token spelling. -/
inductive Atom : List Token → instr → Prop where
  | simple {token op} : Simple token op → Atom [token] op
  | block {tokens ops} (bt : signature.BlockType) : Emits tokens ops →
      Atom ([.block bt] ++ tokens ++ [.end_]) (.BLOCK (blockType bt) ops)
  | loop {tokens ops} (bt : signature.BlockType) : Emits tokens ops →
      Atom ([.loop bt] ++ tokens ++ [.end_]) (.LOOP (blockType bt) ops)
  | ifElse {yesTokens yes noTokens no} (bt : signature.BlockType) :
      Emits yesTokens yes → Emits noTokens no →
      Atom ([.if_ bt] ++ yesTokens ++ [.else_] ++ noTokens ++ [.end_])
        (.IFELSE (blockType bt) yes no)
  | ifEnd {tokens ops} (bt : signature.BlockType) : Emits tokens ops →
      Atom ([.if_ bt] ++ tokens ++ [.end_]) (.IFELSE (blockType bt) ops [])

theorem Atom.emits {tokens op} (h : Atom tokens op) : Emits tokens [op] := by
  cases h with
  | simple hs => simpa using Emits.simple .nil hs
  | block bt hb => simpa using Emits.block bt .nil hb
  | loop bt hb => simpa using Emits.loop bt .nil hb
  | ifElse bt hy hn => simpa using Emits.ifElse bt .nil hy hn
  | ifEnd bt hb => simpa using Emits.ifEnd bt .nil hb

theorem Atom.nonempty {tokens op} (h : Atom tokens op) : tokens ≠ [] := by
  cases h <;> simp

/-- A left-to-right presentation of the same independent syntax relation. -/
inductive Spells : List Token → List instr → Prop where
  | nil : Spells [] []
  | cons {first rest op ops} : Atom first op → Spells rest ops →
      Spells (first ++ rest) (op :: ops)

theorem Spells.append {xs ys ops rest} (hx : Spells xs ops) (hy : Spells ys rest) :
    Spells (xs ++ ys) (ops ++ rest) := by
  induction hx with
  | nil => exact hy
  | cons h _ ih => simpa [List.append_assoc] using Spells.cons h ih

theorem Spells.emits {tokens ops} (h : Spells tokens ops) : Emits tokens ops := by
  induction h with
  | nil => exact .nil
  | cons hop _ ih => simpa using hop.emits.append ih

theorem Emits.spells {tokens ops} (h : Emits tokens ops) : Spells tokens ops := by
  induction h with
  | nil => exact .nil
  | simple _ hs ih =>
    simpa using ih.append (.cons (.simple hs) .nil)
  | block bt _ hb ih _ =>
    simpa [List.append_assoc] using ih.append (.cons (.block bt hb) .nil)
  | loop bt _ hb ih _ =>
    simpa [List.append_assoc] using ih.append (.cons (.loop bt hb) .nil)
  | ifElse bt _ hy hn ih _ _ =>
    simpa [List.append_assoc] using ih.append (.cons (.ifElse bt hy hn) .nil)
  | ifEnd bt _ hb ih _ =>
    simpa [List.append_assoc] using ih.append (.cons (.ifEnd bt hb) .nil)

theorem Emits.empty_iff {tokens} : Emits tokens [] ↔ tokens = [] := by
  constructor
  · intro h
    have hs := h.spells
    cases hs
    rfl
  · rintro rfl
    exact .nil

/-- Split the next instruction off the unread syntax independently of the
streaming validator. Its token span includes all nested delimiters. -/
theorem Emits.cons_iff {tokens op ops} :
    Emits tokens (op :: ops) ↔
      ∃ first rest, tokens = first ++ rest ∧ Atom first op ∧ Emits rest ops := by
  constructor
  · intro h
    have hs := h.spells
    cases hs with
    | cons hop ht => exact ⟨_, _, rfl, hop, ht.emits⟩
  · rintro ⟨first, rest, rfl, hop, ht⟩
    simpa using hop.emits.append ht

theorem Emits.singleton_iff {tokens op} : Emits tokens [op] ↔ Atom tokens op := by
  rw [Emits.cons_iff]
  constructor
  · rintro ⟨first, rest, rfl, hop, ht⟩
    have he := Emits.empty_iff.mp ht
    simpa [he] using hop
  · intro h
    exact ⟨tokens, [], by simp, h, .nil⟩

end Itasca.MultiValue
