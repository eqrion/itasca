import Exec.Code.Local.Lowering.Float.FloatCoreTokens
import Exec.Code.Local.Relations.Common.CoreOpcodes
import Exec.Code.Local.Lowering.Float.FloatOpcode
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Exec.Code

def floatBaseOpcodeValues : List Nat := [139, 140, 141, 142, 143, 144, 145, 153, 154, 155, 156, 157, 158, 159, 146, 147, 148, 149, 150, 151, 152, 160, 161, 162, 163, 164, 165, 166, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 178, 179, 183, 184, 180, 181, 185, 186, 168, 169, 174, 175, 170, 171, 176, 177, 188, 189, 190, 191, 187, 182]

theorem float_base_opcode_of_mem {opcode : U8} (member : opcode.val ∈ floatBaseOpcodeValues) :
    ∃ op : Abs.Float.Instruction, (floatOpcode op).val < 256 ∧ UScalar.cast .U8 (floatOpcode op) = opcode := by
  simp only [floatBaseOpcodeValues,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨.unary .F32 .ABS,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .NEG,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .CEIL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .FLOOR,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .TRUNC,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .NEAREST,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F32 .SQRT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .ABS,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .NEG,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .CEIL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .FLOOR,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .TRUNC,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .NEAREST,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .F64 .SQRT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .ADD,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .SUB,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .MUL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .DIV,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .MIN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .MAX,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F32 .COPYSIGN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .ADD,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .SUB,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .MUL,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .DIV,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .MIN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .MAX,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.binary .F64 .COPYSIGN,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .EQ,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .NE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .LT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .GT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .LE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F32 .GE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .EQ,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .NE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .LT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .GT,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .LE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.compare .F64 .GE,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F32 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F32 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F64 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I32 .F64 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F32 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F32 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F64 .S,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.convert .I64 .F64 .U,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I32 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I32 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I64 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F32 .I64 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I32 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I32 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I64 .S false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.truncate .F64 .I64 .U false,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretFloat .F32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretFloat .F64,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretInt .I32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.reinterpretInt .I64,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.promote,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.demote,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩

def FloatCoreOpcode (opcode : U8) : Prop :=
  CoreOpcode opcode ∨ opcode.val ∈ floatBaseOpcodeValues ∨ opcode = 252#u8

def FloatCoreHead (instruction : instr) : Bool :=
  CoreHead instruction || (Abs.Float.decodeInstruction instruction).isSome

theorem float_core_head {instruction} (supported : Abs.FloatCoreInstr instruction) : FloatCoreHead instruction = true := by
  cases supported with
  | core h => simp [FloatCoreHead,core_head h]
  | scalar op => simp [FloatCoreHead]
  | _ => rfl
set_option maxHeartbeats 2000000 in
theorem numeric_float_core_opcode {opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (supported : Abs.FloatCoreInstr operation.instruction) : FloatCoreOpcode opcode := by
  have head := float_core_head supported
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals first | solve | simp_all [FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues] | contradiction
theorem memory_float_core_opcode {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (_supported : Abs.FloatCoreInstr (operation.op arg)) : FloatCoreOpcode opcode := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]

theorem wasm1_immediate_float_core_opcode {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) (supported : Wasm1.FloatCoreToken token) :
    FloatCoreOpcode opcode := by
  cases encoded <;> try { simp [FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues] }
  all_goals change Abs.FloatCoreInstr _ at supported
  all_goals first
    | exact numeric_float_core_opcode (by assumption) supported
    | exact memory_float_core_opcode _ (by assumption) supported
    | have head := float_core_head supported; contradiction

set_option maxHeartbeats 2000000 in
theorem sign_float_core_opcode {opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (_supported : Abs.FloatCoreInstr operation.instruction) : FloatCoreOpcode opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]

private def simdPureSupported (n : Nat) : Bool :=
  match Wasm2.Simd.pureMeaning n with
  | none => false
  | some operation => FloatCoreHead operation.instruction

private theorem simd_pure_table : ∀ n : Fin 256, simdPureSupported n.val = false := by
  decide

theorem simd_pure_float_core_head {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation) :
    FloatCoreHead operation.instruction = false := by
  have checked := simd_pure_table ⟨opcode, Wasm2.Simd.pure_bound meaning⟩
  simpa only [simdPureSupported, meaning] using checked

theorem simd_pure_not_float_core {opcode operation}
    (meaning : Wasm2.Simd.pureMeaning opcode = some operation)
    (supported : Abs.FloatCoreInstr operation.instruction) : False := by
  have head := float_core_head supported
  rw [simd_pure_float_core_head meaning] at head
  contradiction

set_option maxHeartbeats 4000000 in
theorem simd_lane_not_float_core {opcode operation} (lane : laneidx)
    (meaning : Wasm2.Simd.laneMeaning opcode = some operation)
    (supported : Abs.FloatCoreInstr (operation.instruction lane)) : False := by
  have head := float_core_head supported
  unfold Wasm2.Simd.laneMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

set_option maxHeartbeats 4000000 in
theorem simd_memory_not_float_core {opcode operation} (arg : memarg) (lane : laneidx)
    (meaning : Wasm2.Simd.memoryMeaning opcode = some operation)
    (supported : Abs.FloatCoreInstr (operation.instruction arg lane)) : False := by
  have head := float_core_head supported
  unfold Wasm2.Simd.memoryMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; contradiction

theorem simd_not_float_core {opcode instruction bytes}
    (encoded : Wasm2.Simd.Immediate opcode instruction bytes)
    (supported : Abs.FloatCoreInstr instruction) : False := by
  cases encoded with
  | pure _ _ meaning => exact simd_pure_not_float_core meaning supported
  | lane _ _ _ meaning => exact simd_lane_not_float_core _ meaning supported
  | memory _ _ _ meaning _ _ _ => exact simd_memory_not_float_core _ _ meaning supported
  | memoryLane _ _ _ _ meaning _ _ _ => exact simd_memory_not_float_core _ _ meaning supported
  | constant _ _ _ _ | shuffle _ _ _ _ =>
    have head := float_core_head supported
    contradiction

theorem wasm2_immediate_float_core_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) (supported : Wasm2.FloatCoreToken token) :
    FloatCoreOpcode opcode := by
  cases encoded with
  | block _ | loop _ | if_ _ | else_ | end_ => simp [FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]
  | plain encoded => exact wasm1_immediate_float_core_opcode encoded supported
  | signExtension _ _ meaning => exact sign_float_core_opcode meaning supported
  | saturating _ _ meaning _ => exact Or.inr (Or.inr rfl)
  | reference encoded => cases encoded <;> have head := float_core_head supported <;> contradiction
  | bulk _ _ encoded => cases encoded <;> have head := float_core_head supported <;> contradiction
  | simd _ _ encoded => exact False.elim (simd_not_float_core encoded supported)

end Exec.Code

namespace Itasca.Wasm1
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.float_core_opcode {data start token next}
    (encoded : At data start token next) (supported : FloatCoreToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.FloatCoreOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm1_immediate_float_core_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_float_core_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.FloatCoreInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.FloatCoreOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_float_core_token supported before remaining
  exact atToken.float_core_opcode allowed remaining
end Itasca.Wasm1

namespace Itasca.Wasm2
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.float_core_opcode {data start token next}
    (encoded : At data start token next) (supported : FloatCoreToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.FloatCoreOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm2_immediate_float_core_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_float_core_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.FloatCoreInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.FloatCoreOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_float_core_token supported before remaining
  exact atToken.float_core_opcode allowed remaining
end Itasca.Wasm2
