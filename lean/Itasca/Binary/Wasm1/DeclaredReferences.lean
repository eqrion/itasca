import Itasca.Binary.Wasm1.Encoding
import Itasca.Binary.Wasm2.DeclaredReferences

/-!
# Declared references in Wasm 1.0 syntax

`BodyEncoding.declared` shows that every Wasm 1.0 body meets the `C.refs` condition of
`Spec/DeclaredReferences` for any reference set, because its grammar has no `ref.func`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

open Wasm2 (Token TokensDeclared tokensDeclared_append tokensDeclared_singleton Emits)

set_option maxHeartbeats 2000000 in
/-- Every Wasm 1.0 instruction token meets its obligation, since the grammar has no `ref.func`. -/
theorem Immediate.declared {opcode token bytes} (hi : Immediate opcode token bytes)
    (refs : List funcidx) : token.Declared refs := by
  cases hi with
  | numeric opcode operation hmap =>
    unfold Numeric.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals subst operation
    all_goals simp [Wasm2.Token.Declared, DeclaredReferences.Instruction,
      DeclaredReferences.instructionIndices, Numeric.unary, Numeric.binary,
      Numeric.test, Numeric.relation, Numeric.conversion]
  | memory opcode operation arg hmap _ _ =>
    unfold MemoryMeaning.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals subst operation
    all_goals simp [Wasm2.Token.Declared, DeclaredReferences.Instruction,
      DeclaredReferences.instructionIndices, MemoryMeaning.fullLoad, MemoryMeaning.packedLoad,
      MemoryMeaning.fullStore, MemoryMeaning.packedStore]
  | _ => simp [Wasm2.Token.Declared, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices,
      Spec.i32Const, ScalarConst.i64, ScalarConst.f32, ScalarConst.f64]

/-- A token read at a cursor meets its obligation. -/
theorem At.declared {data start token next} (h : At data start token next) (refs : List funcidx) :
    token.Declared refs := by
  obtain ⟨_, ⟨_, _, _, hi⟩, _⟩ := h
  exact hi.declared refs

end Itasca.Wasm1
