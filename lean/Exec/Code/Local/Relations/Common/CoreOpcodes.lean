import Exec.Code.Local.Relations.Common.CoreTokens
import Exec.Code.Local.Relations.Common.SliceOpcodes
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Exec.Code
/-- The immutable slice plus scalar global, selection, constant and memory opcodes. -/
def CoreOpcode (opcode : U8) : Prop :=
  SliceOpcode opcode ∨ opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62]

def CoreHead (instruction : instr) : Bool :=
  match instruction with
  | .CONST _ _ | .SELECT none | .GLOBAL_GET _ | .GLOBAL_SET _ | .LOAD _ _ _ | .STORE _ _ _ => true
  | _ => SliceHead instruction

theorem slice_head_core {instruction} (head : SliceHead instruction = true) : CoreHead instruction = true := by
  cases instruction <;> first | exact head | rfl | simp [SliceHead] at head

theorem core_head {instruction} (supported : Abs.CoreInstr instruction) : CoreHead instruction = true := by
  cases supported with
  | slice supported => exact slice_head_core (slice_head supported)
  | load op arg => rfl
  | store op arg => rfl
  | _ => rfl

set_option maxHeartbeats 2000000 in
theorem numeric_core_opcode {opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (supported : Abs.CoreInstr operation.instruction) : CoreOpcode opcode := by
  have head := core_head supported
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals first | solve | simp_all [CoreOpcode, SliceOpcode] | contradiction
theorem memory_core_opcode {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (_supported : Abs.CoreInstr (operation.op arg)) : CoreOpcode opcode := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [CoreOpcode, SliceOpcode]

theorem wasm1_immediate_core_opcode {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) (supported : Wasm1.CoreToken token) :
    CoreOpcode opcode := by
  cases encoded <;> try { simp [CoreOpcode, SliceOpcode] }
  all_goals change Abs.CoreInstr _ at supported
  all_goals first
    | exact numeric_core_opcode (by assumption) supported
    | exact memory_core_opcode _ (by assumption) supported
    | have head := core_head supported; contradiction

set_option maxHeartbeats 2000000 in
theorem sign_core_opcode {opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (_supported : Abs.CoreInstr operation.instruction) : CoreOpcode opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [CoreOpcode, SliceOpcode]

set_option maxHeartbeats 2000000 in
theorem saturating_not_core {opcode operation}
    (meaning : Wasm2.NumericExtensions.saturatingMeaning opcode = some operation)
    (supported : Abs.CoreInstr operation.instruction) : False := by
  have head := core_head supported
  unfold Wasm2.NumericExtensions.saturatingMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

private def simdPureSupported (n : Nat) : Bool :=
  match Wasm2.Simd.pureMeaning n with
  | none => false
  | some operation => CoreHead operation.instruction

private theorem simd_pure_table : ∀ n : Fin 256, simdPureSupported n.val = false := by
  decide

theorem simd_pure_core_head {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation) :
    CoreHead operation.instruction = false := by
  have checked := simd_pure_table ⟨opcode, Wasm2.Simd.pure_bound meaning⟩
  simpa only [simdPureSupported, meaning] using checked

theorem simd_pure_not_core {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation)
    (supported : Abs.CoreInstr operation.instruction) : False := by
  have head := core_head supported
  rw [simd_pure_core_head meaning] at head
  contradiction

set_option maxHeartbeats 4000000 in
theorem simd_lane_not_core {opcode operation} (lane : laneidx)
    (meaning : Wasm2.Simd.laneMeaning opcode = some operation)
    (supported : Abs.CoreInstr (operation.instruction lane)) : False := by
  have head := core_head supported
  unfold Wasm2.Simd.laneMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

set_option maxHeartbeats 4000000 in
theorem simd_memory_not_core {opcode operation} (arg : memarg) (lane : laneidx)
    (meaning : Wasm2.Simd.memoryMeaning opcode = some operation)
    (supported : Abs.CoreInstr (operation.instruction arg lane)) : False := by
  have head := core_head supported
  unfold Wasm2.Simd.memoryMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

theorem simd_not_core {opcode instruction bytes}
    (encoded : Wasm2.Simd.Immediate opcode instruction bytes)
    (supported : Abs.CoreInstr instruction) : False := by
  cases encoded with
  | pure _ _ meaning => exact simd_pure_not_core meaning supported
  | lane _ _ _ meaning => exact simd_lane_not_core _ meaning supported
  | memory _ _ _ meaning _ _ _ => exact simd_memory_not_core _ _ meaning supported
  | memoryLane _ _ _ _ meaning _ _ _ => exact simd_memory_not_core _ _ meaning supported
  | constant _ _ _ _ | shuffle _ _ _ _ =>
    have head := core_head supported
    contradiction

theorem wasm2_immediate_core_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) (supported : Wasm2.CoreToken token) :
    CoreOpcode opcode := by
  cases encoded with
  | block _ | loop _ | if_ _ | else_ | end_ => simp [CoreOpcode, SliceOpcode]
  | plain encoded => exact wasm1_immediate_core_opcode encoded supported
  | signExtension _ _ meaning => exact sign_core_opcode meaning supported
  | saturating _ _ meaning _ => exact False.elim (saturating_not_core meaning supported)
  | reference encoded => cases encoded <;> have head := core_head supported <;> contradiction
  | bulk _ _ encoded => cases encoded <;> have head := core_head supported <;> contradiction
  | simd _ _ encoded => exact False.elim (simd_not_core encoded supported)

end Exec.Code

namespace Itasca.Wasm1
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.core_opcode {data start token next}
    (encoded : At data start token next) (supported : CoreToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.CoreOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm1_immediate_core_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_core_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.CoreInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.CoreOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_core_token supported before remaining
  exact atToken.core_opcode allowed remaining
end Itasca.Wasm1

namespace Itasca.Wasm2
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.core_opcode {data start token next}
    (encoded : At data start token next) (supported : CoreToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.CoreOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm2_immediate_core_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_core_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.CoreInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.CoreOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_core_token supported before remaining
  exact atToken.core_opcode allowed remaining
end Itasca.Wasm2
