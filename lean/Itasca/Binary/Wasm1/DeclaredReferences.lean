import Itasca.Binary.Wasm1.Encoding
import Itasca.Spec.DeclaredReferences

open Aeneas Aeneas.Std

namespace Itasca.Wasm

/-- Only reference instructions carry declaration obligations in a flat stream. -/
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
    TokensDeclared refs [token] ↔ token.Declared refs := by simp [TokensDeclared]

@[simp] theorem tokensDeclared_cons (refs : List funcidx) (token : Token) (tokens : List Token) :
    TokensDeclared refs (token :: tokens) ↔ token.Declared refs ∧ TokensDeclared refs tokens := by
  simp [TokensDeclared, or_imp, forall_and]

set_option maxHeartbeats 2000000 in
/-- The original byte grammar contains no reference-producing function literal. -/
theorem Immediate.declared {opcode token bytes} (hi : Immediate opcode token bytes)
    (refs : List funcidx) : token.Declared refs := by
  cases hi with
  | numeric opcode operation hmap =>
    unfold Numeric.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals try contradiction
    all_goals subst operation
    all_goals simp [Token.Declared, DeclaredReferences.Instruction,
      DeclaredReferences.instructionIndices, Numeric.unary, Numeric.binary,
      Numeric.test, Numeric.relation, Numeric.conversion]
  | memory opcode operation arg hmap _ _ =>
    unfold MemoryMeaning.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals try contradiction
    all_goals subst operation
    all_goals simp [Token.Declared, DeclaredReferences.Instruction,
      DeclaredReferences.instructionIndices, MemoryMeaning.fullLoad, MemoryMeaning.packedLoad,
      MemoryMeaning.fullStore, MemoryMeaning.packedStore]
  | _ => simp [Token.Declared, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices,
      Core.i32Const, ScalarConst.i64, ScalarConst.f32, ScalarConst.f64]

theorem At.declared {data start token next} (h : At data start token next) (refs : List funcidx) :
    token.Declared refs := by
  obtain ⟨_, ⟨_, _, _, hi⟩, _⟩ := h
  exact hi.declared refs

theorem Consumed.declared {data start tokens next} (h : Consumed data start tokens next)
    (refs : List funcidx) : TokensDeclared refs tokens := by
  induction h with
  | nil => simp
  | snoc _ ha ih => exact (tokensDeclared_append _ _ _).mpr ⟨ih, (tokensDeclared_singleton _ _).mpr (ha.declared refs)⟩

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

/-- Independently encoded Wasm 1.0 bodies meet the declaration supplement for
any declaration set; their binary grammar excludes all ref.func leaves. -/
theorem BodyEncoding.declared {data ops} (h : BodyEncoding data ops) (refs : List funcidx) :
    DeclaredReferences.Instructions refs ops := by
  obtain ⟨tokens, next, hc, _, inner, rfl, he⟩ := h
  have hd := ((tokensDeclared_append _ _ _).mp (hc.declared refs)).1
  exact (he.declared_iff refs).mp hd

end Itasca.Wasm
