import Itasca.Binary.Wasm2.Simd
import Mathlib.Tactic.IntervalCases

/-!
# SIMD opcode tables

`pure_table`, `lane_table` and `memory_table` show that the extracted tables `code.simd_signature`,
`code.simd_lane_info` and `code.simd_memory_info` agree with the independent meanings
`pureMeaning`, `laneMeaning` and `memoryMeaning`, for every `u32` subopcode.
`Signature.runtime`, `LaneOperation.runtime` and `MemoryOperation.runtime` map the independent
classification to the extracted representation.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- The extracted `code.SimdSignature` for an independent pure SIMD signature. -/
def Signature.runtime : Signature → code.SimdSignature
  | .unary => .Unary
  | .binary => .Binary
  | .ternary => .Ternary
  | .test => .Test
  | .shift => .Shift
  | .splatI32 => .SplatI32
  | .splatI64 => .SplatI64
  | .splatF32 => .SplatF32
  | .splatF64 => .SplatF64

/-- The scalar type, lane count and replace flag that `code.simd_lane_info` returns for a lane
operation. -/
def LaneOperation.runtime (op : LaneOperation) : wasm_types.ValueType × U8 × Bool :=
  (match op.scalar with
   | .I32 => .I32 | .I64 => .I64 | .F32 => .F32 | .F64 => .F64,
   U8.ofNatCore op.count (by cases op <;> decide), op.replace)

/-- The natural alignment, store flag and lane count that `code.simd_memory_info` returns for a
memory operation. -/
def MemoryOperation.runtime (op : MemoryOperation) : U32 × Bool × U8 :=
  (U32.ofNatCore op.naturalAlign (by cases op <;> decide), op.store,
   U8.ofNatCore op.laneCount (by cases op <;> decide))

end Itasca.Wasm2.Simd

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
/-- The runtime lane table agrees with independent lane operation meanings. -/
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
/-- The runtime memory table agrees with independent memory operation meanings. -/
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
