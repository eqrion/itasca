import Itasca.Binary.Wasm1.Syntax

/-!
# Instruction-by-instruction view of Wasm 1.0 syntax

`Atom` gives the complete token spelling of one instruction, and `Spells` is the left-to-right
form of `Emits`. `Emits.cons_iff` splits the next instruction and its tokens, including nested
delimiters, off the remaining syntax.
-/

namespace Itasca.Wasm1

/-- The complete flat token spelling of a single instruction, including nested delimiters. -/
inductive Atom : List Token → instr → Prop where
  | simple {token op} : Simple token op → Atom [token] op
  | block {tokens ops} (bt : code.BlockType) : Emits tokens ops →
      Atom ([.block bt] ++ tokens ++ [.end_]) (.BLOCK (Control.blockType bt) ops)
  | loop {tokens ops} (bt : code.BlockType) : Emits tokens ops →
      Atom ([.loop bt] ++ tokens ++ [.end_]) (.LOOP (Control.blockType bt) ops)
  | ifElse {yesTokens yes noTokens no} (bt : code.BlockType) :
      Emits yesTokens yes → Emits noTokens no →
      Atom ([.if_ bt] ++ yesTokens ++ [.else_] ++ noTokens ++ [.end_])
        (.IFELSE (Control.blockType bt) yes no)
  | ifEnd {tokens ops} (bt : code.BlockType) : Emits tokens ops →
      Atom ([.if_ bt] ++ tokens ++ [.end_]) (.IFELSE (Control.blockType bt) ops [])

/-- An atom emits its instruction. -/
theorem Atom.emits {tokens op} (h : Atom tokens op) : Emits tokens [op] := by
  cases h with
  | simple hs => simpa using Emits.simple .nil hs
  | block bt hb => simpa using Emits.block bt .nil hb
  | loop bt hb => simpa using Emits.loop bt .nil hb
  | ifElse bt hy hn => simpa using Emits.ifElse bt .nil hy hn
  | ifEnd bt hb => simpa using Emits.ifEnd bt .nil hb

theorem Atom.nonempty {tokens op} (h : Atom tokens op) : tokens ≠ [] := by
  cases h <;> simp

/-- A left-to-right presentation of `Emits` as a concatenation of atoms. -/
inductive Spells : List Token → List instr → Prop where
  | nil : Spells [] []
  | cons {first rest op ops} : Atom first op → Spells rest ops →
      Spells (first ++ rest) (op :: ops)

theorem Spells.append {xs ys ops rest} (hx : Spells xs ops) (hy : Spells ys rest) :
    Spells (xs ++ ys) (ops ++ rest) := by
  induction hx with
  | nil => exact hy
  | cons h _ ih => simpa [List.append_assoc] using Spells.cons h ih

/-- `Spells` implies `Emits`. -/
theorem Spells.emits {tokens ops} (h : Spells tokens ops) : Emits tokens ops := by
  induction h with
  | nil => exact .nil
  | cons hop _ ih => simpa using hop.emits.append ih

/-- `Emits` implies `Spells`. -/
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

/-- Splits the first instruction and its tokens, including all nested delimiters, off the rest of
the syntax. -/
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

/-- A token list emits one instruction exactly when it is that instruction's atom. -/
theorem Emits.singleton_iff {tokens op} : Emits tokens [op] ↔ Atom tokens op := by
  rw [Emits.cons_iff]
  constructor
  · rintro ⟨first, rest, rfl, hop, ht⟩
    have he := Emits.empty_iff.mp ht
    simpa [he] using hop
  · intro h
    exact ⟨tokens, [], by simp, h, .nil⟩

end Itasca.Wasm1
