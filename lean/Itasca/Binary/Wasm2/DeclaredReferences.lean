import Itasca.Binary.Wasm2.Syntax
import Itasca.Spec.DeclaredReferences

namespace Itasca.MultiValue

/-- The flat stream carries reference obligations only at instruction tokens. -/
def Token.Declared (refs : List funcidx) : Token → Prop
  | .plain op => DeclaredReferences.Instruction refs op
  | _ => True

def TokensDeclared (refs : List funcidx) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.Declared refs

@[simp] theorem tokensDeclared_nil (refs : List funcidx) : TokensDeclared refs [] := by
  simp [TokensDeclared]

@[simp] theorem tokensDeclared_append (refs : List funcidx) (a b : List Token) :
    TokensDeclared refs (a ++ b) ↔ TokensDeclared refs a ∧ TokensDeclared refs b := by
  simp [TokensDeclared, or_imp, forall_and]

@[simp] theorem tokensDeclared_singleton (refs : List funcidx) (token : Token) :
    TokensDeclared refs [token] ↔ token.Declared refs := by
  simp [TokensDeclared]

@[simp] theorem tokensDeclared_cons (refs : List funcidx) (token : Token) (tokens : List Token) :
    TokensDeclared refs (token :: tokens) ↔ token.Declared refs ∧ TokensDeclared refs tokens := by
  simp [TokensDeclared, or_imp, forall_and]

/-- Folding flat structured tokens preserves exactly the independent
declared-reference condition, in both directions. -/
theorem Emits.declared_iff {tokens ops} (h : Emits tokens ops) (refs : List funcidx) :
    TokensDeclared refs tokens ↔ DeclaredReferences.Instructions refs ops := by
  induction h with
  | nil => simp
  | simple _ hs ih =>
    cases hs
    simp [Token.Declared, ih]
  | block bt _ _ ih hb => simp [Token.Declared, ih, hb]
  | loop bt _ _ ih hb => simp [Token.Declared, ih, hb]
  | ifElse bt _ _ _ ih ht he => simp [Token.Declared, ih, ht, he, and_assoc]
  | ifEnd bt _ _ ih hb => simp [Token.Declared, ih, hb]

theorem BodyTokens.declared_iff {tokens ops} (h : BodyTokens tokens ops) (refs : List funcidx) :
    TokensDeclared refs tokens ↔ DeclaredReferences.Instructions refs ops := by
  obtain ⟨inner, rfl, he⟩ := h
  simpa [Token.Declared] using he.declared_iff refs

end Itasca.MultiValue
