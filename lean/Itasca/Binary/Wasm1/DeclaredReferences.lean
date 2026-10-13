import Itasca.Binary.Wasm1.Encoding
import Itasca.Spec.DeclaredReferences

/-!
# Declared references in Wasm 1.0 syntax

Transfers the `C.refs` condition of `Spec/DeclaredReferences` to flat tokens: `Emits.declared_iff`
relates `TokensDeclared` to `DeclaredReferences.Instructions`, and `BodyEncoding.declared` shows
that every Wasm 1.0 body meets the condition for any reference set, because its grammar has no
`ref.func`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- Only plain instruction tokens carry declared-reference obligations. -/
def Token.Declared (refs : List funcidx) : Token → Prop
  | .plain op => DeclaredReferences.Instruction refs op
  | _ => True

/-- Every token of the list meets its declared-reference obligation. -/
def TokensDeclared (refs : List funcidx) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.Declared refs

@[simp] theorem tokensDeclared_nil (refs : List funcidx) : TokensDeclared refs [] := by
  simp [TokensDeclared]

@[simp] theorem tokensDeclared_append (refs : List funcidx) (a b : List Token) :
    TokensDeclared refs (a ++ b) ↔ TokensDeclared refs a ∧ TokensDeclared refs b := by
  simp [TokensDeclared, or_imp, forall_and]

@[simp] theorem tokensDeclared_singleton (refs : List funcidx) (token : Token) :
    TokensDeclared refs [token] ↔ token.Declared refs := by simp [TokensDeclared]

@[simp] theorem tokensDeclared_cons (refs : List funcidx) (token : Token) (tokens : List Token) :
    TokensDeclared refs (token :: tokens) ↔ token.Declared refs ∧ TokensDeclared refs tokens := by
  simp [TokensDeclared, or_imp, forall_and]

set_option maxHeartbeats 2000000 in
/-- Every Wasm 1.0 instruction token meets its obligation, since the grammar has no `ref.func`. -/
theorem Immediate.declared {opcode token bytes} (hi : Immediate opcode token bytes)
    (refs : List funcidx) : token.Declared refs := by
  cases hi with
  | numeric opcode operation hmap =>
    unfold Numeric.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals subst operation
    all_goals simp [Token.Declared, DeclaredReferences.Instruction,
      DeclaredReferences.instructionIndices, Numeric.unary, Numeric.binary,
      Numeric.test, Numeric.relation, Numeric.conversion]
  | memory opcode operation arg hmap _ _ =>
    unfold MemoryMeaning.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals subst operation
    all_goals simp [Token.Declared, DeclaredReferences.Instruction,
      DeclaredReferences.instructionIndices, MemoryMeaning.fullLoad, MemoryMeaning.packedLoad,
      MemoryMeaning.fullStore, MemoryMeaning.packedStore]
  | _ => simp [Token.Declared, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices,
      Spec.i32Const, ScalarConst.i64, ScalarConst.f32, ScalarConst.f64]

/-- A token read at a cursor meets its obligation. -/
theorem At.declared {data start token next} (h : At data start token next) (refs : List funcidx) :
    token.Declared refs := by
  obtain ⟨_, ⟨_, _, _, hi⟩, _⟩ := h
  exact hi.declared refs

/-- The tokens of a consumed span meet their obligations. -/
theorem Consumed.declared {data start tokens next} (h : Consumed data start tokens next)
    (refs : List funcidx) : TokensDeclared refs tokens := by
  induction h with
  | nil => simp
  | snoc _ ha ih => exact (tokensDeclared_append _ _ _).mpr ⟨ih, (tokensDeclared_singleton _ _).mpr (ha.declared refs)⟩

/-- Tokens meet their obligations exactly when the instructions they spell do. -/
theorem Emits.declared_iff {tokens ops} (h : Emits tokens ops) (refs : List funcidx) :
    TokensDeclared refs tokens ↔ DeclaredReferences.Instructions refs ops := by
  induction h with
  | nil => simp
  | simple _ hs ih =>
    cases hs
    simp [Token.Declared, ih]
  | block bt _ _ ih hb => simp [Token.Declared, ih, hb]
  | loop bt _ _ ih hb => simp [Token.Declared, ih, hb]
  | ifElse bt _ _ _ ih ht he => simp [Token.Declared, ih, ht, he]
  | ifEnd bt _ _ ih hb => simp [Token.Declared, ih, hb]

/-- A Wasm 1.0 body meets the declared-reference condition for any reference set. -/
theorem BodyEncoding.declared {data ops} (h : BodyEncoding data ops) (refs : List funcidx) :
    DeclaredReferences.Instructions refs ops := by
  obtain ⟨tokens, next, hc, _, inner, rfl, he⟩ := h
  have hd := ((tokensDeclared_append _ _ _).mp (hc.declared refs)).1
  exact (he.declared_iff refs).mp hd

end Itasca.Wasm1
