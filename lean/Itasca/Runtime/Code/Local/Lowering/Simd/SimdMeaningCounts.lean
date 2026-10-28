import Itasca.Runtime.Code.Local.Lowering.Simd.SimdEmission
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096

theorem SimdImmediateMeaning.input_positive {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) : 0 < input.length := by
  cases meaning with
  | pure opcode immediate op meaning => cases op.signature <;> decide
  | lane opcode immediate op meaning lane position => cases op <;> decide
  | memory opcode immediate op meaning argument lane memory available offset position => cases op <;> decide
  | shuffle => decide

private theorem not_store_of_pure (opcode : U32) (op : Operation)
    (meaning : pureMeaning opcode.val = some op) : simdStores opcode = false := by
  unfold simdStores
  split
  · rename_i eleven
    have number : opcode.val = 11 := by simpa using congrArg UScalar.val eleven
    rw [number] at meaning
    change none = some op at meaning
    contradiction
  · split
    · rename_i lower
      have notUpper : ¬ opcode ≤ 91#u32 := by
        intro upper
        have low : 88 ≤ opcode.val := by scalar_tac
        have high : opcode.val ≤ 91 := by scalar_tac
        have cases : opcode.val = 88 ∨ opcode.val = 89 ∨ opcode.val = 90 ∨ opcode.val = 91 := by omega
        rcases cases with h | h | h | h
        all_goals rw [h] at meaning
        all_goals change none = some op at meaning
        all_goals contradiction
      simp [notUpper]
    · rfl

private theorem not_store_of_lane (opcode : U32) (op : LaneOperation)
    (meaning : laneMeaning opcode.val = some op) : simdStores opcode = false := by
  unfold simdStores
  split
  · rename_i eleven
    have number : opcode.val = 11 := by simpa using congrArg UScalar.val eleven
    rw [number] at meaning
    change none = some op at meaning
    contradiction
  · split
    · rename_i lower
      have notUpper : ¬ opcode ≤ 91#u32 := by
        intro upper
        have low : 88 ≤ opcode.val := by scalar_tac
        have high : opcode.val ≤ 91 := by scalar_tac
        have cases : opcode.val = 88 ∨ opcode.val = 89 ∨ opcode.val = 90 ∨ opcode.val = 91 := by omega
        rcases cases with h | h | h | h
        all_goals rw [h] at meaning
        all_goals change none = some op at meaning
        all_goals contradiction
      simp [notUpper]
    · rfl

private theorem store_of_memory (opcode : U32) (op : MemoryOperation)
    (meaning : memoryMeaning opcode.val = some op) : simdStores opcode = op.store := by
  unfold memoryMeaning at meaning
  split at meaning
  all_goals simp only [Option.some.injEq, reduceCtorEq] at meaning
  all_goals first | contradiction | subst op
  all_goals simp only [simdStores,MemoryOperation.store]
  all_goals split_ifs <;> scalar_tac

theorem SimdImmediateMeaning.output_count {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) :
    output.length = if simdStores opcode then 0 else 1 := by
  cases meaning with
  | pure opcode immediate op meaning =>
    rw [not_store_of_pure opcode op meaning]
    cases op.signature <;> rfl
  | lane opcode immediate op meaning lane position =>
    rw [not_store_of_lane opcode op meaning]
    cases op <;> rfl
  | memory opcode immediate op meaning argument lane memory available offset position =>
    rw [store_of_memory opcode op meaning]
    cases op <;> rfl
  | shuffle => rfl
end Itasca.Runtime.Code
