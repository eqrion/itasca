import Mathlib.Tactic.IntervalCases
import Itasca.Wasm2.Simd.Runtime

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The runtime pure signature table agrees with independent instruction meanings. -/
theorem pure_table (opcode : U32) :
    code.simd_signature opcode = .ok ((pureMeaning opcode.val).map (fun op => op.signature.runtime)) := by
  by_cases hb : opcode.val < 256
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 256 at hb
    interval_cases n <;> (with_unfolding_all rfl)
  · have hnone : pureMeaning opcode.val = none := by
      cases hm : pureMeaning opcode.val with
      | none => rfl
      | some op => exact False.elim (hb (pure_bound hm))
    rw [hnone]
    simp only [Option.map_none]
    have hn : opcode ≥ 256#u32 := by scalar_tac
    unfold code.simd_signature
    rw [if_pos hn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem lane_table (opcode : U32) :
    code.simd_lane_info opcode = .ok ((laneMeaning opcode.val).map LaneOperation.runtime) := by
  by_cases hb : opcode.val < 256
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 256 at hb
    interval_cases n <;> (with_unfolding_all rfl)
  · have hnone : laneMeaning opcode.val = none := by
      unfold laneMeaning
      split <;> first | rfl | omega
    rw [hnone]
    simp only [Option.map_none]
    unfold code.simd_lane_info
    split <;> first | rfl | (exfalso; apply hb; decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem memory_table (opcode : U32) :
    code.simd_memory_info opcode = .ok ((memoryMeaning opcode.val).map MemoryOperation.runtime) := by
  by_cases hb : opcode.val < 256
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 256 at hb
    interval_cases n <;> (with_unfolding_all rfl)
  · have hnone : memoryMeaning opcode.val = none := by
      unfold memoryMeaning
      split <;> first | rfl | omega
    rw [hnone]
    simp only [Option.map_none]
    unfold code.simd_memory_info
    split <;> first | rfl | (exfalso; apply hb; decide)

end Itasca.Wasm2.Simd
