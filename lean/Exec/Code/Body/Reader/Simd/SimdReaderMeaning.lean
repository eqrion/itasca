import Exec.Code.Local.Capacity.SimdMeaningBound
import Exec.Code.Local.Lowering.Simd.SimdBits
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Simd

/-- Ordinary lane callbacks encode the checked lane index in the first scalar
immediate, outside the separate memory-lane opcode range. -/
theorem simd_lane_callback_meaning (C : context) (sub : U32) (op : LaneOperation) (lane : U8)
    (meaning : laneMeaning sub.val = some op) :
    SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      op.inputs (op.instruction (.mk_uN lane.val)) op.outputs := by
  have small : sub.val < 84 := by
    unfold laneMeaning at meaning
    split at meaning <;> first | contradiction | omega
  apply SimdImmediateMeaning.lane sub _ op meaning lane
  have outside : ¬ 84#u32 ≤ sub := by scalar_tac
  simp only [simdImmediate,simdLane,if_neg outside,UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem simd_memory_callback_meaning (C : context) (sub : U32) (op : MemoryOperation)
    (arg : code.MemArg) (memory : memtype)
    (meaning : memoryMeaning sub.val = some op) (full : op.laneCount = 0)
    (available : C.MEMS[0]? = some memory) :
    SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      op.inputs (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)) op.outputs := by
  apply SimdImmediateMeaning.memory sub _ op meaning (MemoryMeaning.memArg arg) 0#u8 memory available rfl
  simp only [full,ne_eq,not_true_eq_false,false_implies]

theorem simd_memory_lane_callback_meaning (C : context) (sub : U32) (op : MemoryOperation)
    (arg : code.MemArg) (lane : U8) (memory : memtype)
    (meaning : memoryMeaning sub.val = some op) (laned : op.laneCount ≠ 0)
    (available : C.MEMS[0]? = some memory) :
    SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane))
      op.inputs (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val)) op.outputs := by
  have range : 84 ≤ sub.val ∧ sub.val ≤ 91 := by
    unfold memoryMeaning at meaning
    split at meaning <;> first | contradiction | cases meaning
    all_goals simp_all [MemoryOperation.laneCount]
  apply SimdImmediateMeaning.memory sub _ op meaning (MemoryMeaning.memArg arg) lane memory available rfl
  intro _
  have lower : 84#u32 ≤ sub := by scalar_tac
  have upper : sub ≤ 91#u32 := by scalar_tac
  simp only [simdImmediate,simdLane,if_pos lower,if_pos upper,UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt (by scalar_tac),Nat.mod_eq_of_lt (by scalar_tac)]

theorem simd_shuffle_callback_meaning (C : context) (lo hi : U64) :
    SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits lo hi))
      [.V128,.V128] (shuffle lo hi) [.V128] := by
  exact .shuffle _ lo hi (initializerBits_val lo hi)

theorem SimdImmediateMeaning.not_constant {C sub immediate input source output}
    (meaning : SimdImmediateMeaning C sub immediate input source output) : sub.val ≠ 12 := by
  intro equal
  cases meaning with
  | pure sub immediate op meaning => rw [equal] at meaning; cases meaning
  | lane sub immediate op meaning lane position => rw [equal] at meaning; cases meaning
  | memory sub immediate op meaning arg lane memory available offset position => rw [equal] at meaning; cases meaning
  | shuffle => contradiction
end Exec.Code
