import Itasca.Wasm1.Run
import Itasca.Wasm1.ProfileSyntax
import Itasca.Binary.Wasm1.NumericMeaning
import Itasca.Binary.Wasm1.MemoryMeaning

/-!
# Wasm 1.0 body input proposition

`Wasm1.Body` is the input proposition of Wasm 1.0 body completeness: an independent binary
encoding, generated SpecTec typing, and the Wasm 1.0 profile. `Numeric.opcode_profile` and
`MemoryMeaning.opcode_profile` show that every numeric and memory opcode meaning satisfies the
profile.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The input proposition of completeness: the bytes encode an instruction list that has
generated declarative typing and satisfies the Wasm 1.0 profile. The size cap, the environment
signatures, and the result shape are separate hypotheses of the public completeness theorem. -/
def Body (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : Prop :=
  ∃ ops, Wasm1.BodyEncoding data ops ∧ Wasm1.FunctionTyped env ctx bt ops ∧
    Instructions (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops

/-- The profile can be dropped from `Wasm1.Body`. -/
theorem Body.validated {data env ctx bt} (h : Body data env ctx bt) :
    Wasm1.Validated data env ctx bt := by
  obtain ⟨ops, hb, ht, _⟩ := h
  exact ⟨ops, hb, ht⟩

end Itasca.Wasm1

open Aeneas Aeneas.Std

namespace Itasca

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Every numeric opcode meaning satisfies the Wasm 1.0 profile in any context. -/
theorem Numeric.opcode_profile (opcode : U8) (op : Numeric.Operation)
    (hmap : Numeric.opcodeMeaning opcode = some op) (C : context) :
    Wasm1.Instruction C op.instruction := by
  unfold Numeric.opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
  all_goals first | contradiction | subst op; exact .leaf _ _ trivial

set_option maxRecDepth 4096 in
/-- Every memory opcode meaning satisfies the Wasm 1.0 profile in any context. -/
theorem MemoryMeaning.opcode_profile (opcode : U8) (op : MemoryMeaning.Operation)
    (hmap : MemoryMeaning.opcodeMeaning opcode = some op) (C : context) (arg : code.MemArg) :
    Wasm1.Instruction C (op.op arg) := by
  unfold MemoryMeaning.opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
  all_goals first | contradiction | subst op; exact .leaf _ _ trivial

end Itasca
