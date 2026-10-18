import Exec.Code.Local.Control.Common.CumulativeTokens
import Exec.Code.Local.Lowering.Float.FloatCoreOpcodes
import Exec.Code.Local.Relations.Common.CoreOpcodes
import Exec.Code.Local.Lowering.Float.FloatOpcode
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Exec.Code
def CumulativeOpcode (opcode : U8) : Prop :=
  FloatCoreOpcode opcode ∨ opcode.val ∈ [37,38,63,64,208,209,210] ∨ opcode = 17#u8

def CumulativeHead (instruction : instr) : Bool :=
  FloatCoreHead instruction || (Abs.Stateful.decodeInstruction instruction).isSome ||
    (match instruction with | .CALL_INDIRECT .. => true | _ => false)

theorem cumulative_head {instruction} (supported : Abs.CumulativeInstr instruction) : CumulativeHead instruction = true := by
  cases supported with
  | core h => simp [CumulativeHead,float_core_head h]
  | stateful op => simp [CumulativeHead]
  | _ => rfl
set_option maxHeartbeats 2000000 in
theorem numeric_cumulative_opcode {opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (supported : Abs.CumulativeInstr operation.instruction) : CumulativeOpcode opcode := by
  have head := cumulative_head supported
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals first | solve | simp_all [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues] | contradiction
theorem memory_cumulative_opcode {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (_supported : Abs.CumulativeInstr (operation.op arg)) : CumulativeOpcode opcode := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]

theorem wasm1_immediate_cumulative_opcode {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) (supported : Wasm1.CumulativeToken token) :
    CumulativeOpcode opcode := by
  cases encoded <;> try { simp [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues] }
  all_goals change Abs.CumulativeInstr _ at supported
  all_goals first
    | exact numeric_cumulative_opcode (by assumption) supported
    | exact memory_cumulative_opcode _ (by assumption) supported
    | have head := cumulative_head supported; contradiction

set_option maxHeartbeats 2000000 in
theorem sign_cumulative_opcode {opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (_supported : Abs.CumulativeInstr operation.instruction) : CumulativeOpcode opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]

private def simdPureSupported (n : Nat) : Bool :=
  match Wasm2.Simd.pureMeaning n with
  | none => false
  | some operation => CumulativeHead operation.instruction

private theorem simd_pure_table : ∀ n : Fin 256, simdPureSupported n.val = false := by
  decide

theorem simd_pure_cumulative_head {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation) :
    CumulativeHead operation.instruction = false := by
  have checked := simd_pure_table ⟨opcode, Wasm2.Simd.pure_bound meaning⟩
  simpa only [simdPureSupported, meaning] using checked

theorem simd_pure_not_cumulative {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation)
    (supported : Abs.CumulativeInstr operation.instruction) : False := by
  have head := cumulative_head supported
  rw [simd_pure_cumulative_head meaning] at head
  contradiction

set_option maxHeartbeats 4000000 in
theorem simd_lane_not_cumulative {opcode operation} (lane : laneidx)
    (meaning : Wasm2.Simd.laneMeaning opcode = some operation)
    (supported : Abs.CumulativeInstr (operation.instruction lane)) : False := by
  have head := cumulative_head supported
  unfold Wasm2.Simd.laneMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

set_option maxHeartbeats 4000000 in
theorem simd_memory_not_cumulative {opcode operation} (arg : memarg) (lane : laneidx)
    (meaning : Wasm2.Simd.memoryMeaning opcode = some operation)
    (supported : Abs.CumulativeInstr (operation.instruction arg lane)) : False := by
  have head := cumulative_head supported
  unfold Wasm2.Simd.memoryMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

theorem simd_not_cumulative {opcode instruction bytes}
    (encoded : Wasm2.Simd.Immediate opcode instruction bytes)
    (supported : Abs.CumulativeInstr instruction) : False := by
  cases encoded with
  | pure _ _ meaning => exact simd_pure_not_cumulative meaning supported
  | lane _ _ _ meaning => exact simd_lane_not_cumulative _ meaning supported
  | memory _ _ _ meaning _ _ _ => exact simd_memory_not_cumulative _ _ meaning supported
  | memoryLane _ _ _ _ meaning _ _ _ => exact simd_memory_not_cumulative _ _ meaning supported
  | constant _ _ _ _ | shuffle _ _ _ _ =>
    have head := cumulative_head supported
    contradiction

theorem wasm2_immediate_cumulative_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) (supported : Wasm2.CumulativeToken token) :
    CumulativeOpcode opcode := by
  cases encoded with
  | block _ | loop _ | if_ _ | else_ | end_ => simp [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]
  | plain encoded => exact wasm1_immediate_cumulative_opcode encoded supported
  | signExtension _ _ meaning => exact sign_cumulative_opcode meaning supported
  | saturating _ _ meaning _ => exact Or.inl (Or.inr (Or.inr rfl))
  | reference encoded =>
    cases encoded <;> first
      | solve | simp [CumulativeOpcode]
      | have head := cumulative_head supported; contradiction
  | bulk _ _ encoded => exact Or.inl (Or.inr (Or.inr rfl))
  | simd _ _ encoded => exact False.elim (simd_not_cumulative encoded supported)

end Exec.Code

namespace Itasca.Wasm1
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.cumulative_opcode {data start token next}
    (encoded : At data start token next) (supported : CumulativeToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.CumulativeOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm1_immediate_cumulative_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_cumulative_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.CumulativeInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.CumulativeOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_cumulative_token supported before remaining
  exact atToken.cumulative_opcode allowed remaining
end Itasca.Wasm1

namespace Itasca.Wasm2
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.cumulative_opcode {data start token next}
    (encoded : At data start token next) (supported : CumulativeToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.CumulativeOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm2_immediate_cumulative_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_cumulative_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.CumulativeInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.CumulativeOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_cumulative_token supported before remaining
  exact atToken.cumulative_opcode allowed remaining
end Itasca.Wasm2
