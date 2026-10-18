import Exec.Code.Local.Control.Common.CumulativeOpcodes
import Exec.Code.Local.Relations.Common.ExecutableTokens
import Exec.Code.Local.Source.SourceExecutableBody
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Exec.Code

/-- Every reader opcode of the complete executable profile, including branch
tables and explicitly typed select. -/
def ExecutableOpcode (opcode : U8) : Prop :=
  CumulativeOpcode opcode ∨ opcode = 253#u8 ∨ opcode = 14#u8 ∨ opcode = 28#u8

set_option maxHeartbeats 2000000 in
theorem numeric_executable_opcode {opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation) : ExecutableOpcode opcode := by
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals simp_all [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode,floatBaseOpcodeValues]

theorem memory_executable_opcode {opcode operation}
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation) : ExecutableOpcode opcode := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals simp_all [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode,floatBaseOpcodeValues]

theorem wasm1_immediate_executable_opcode {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) : ExecutableOpcode opcode := by
  cases encoded <;> try { simp [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode,floatBaseOpcodeValues] }
  all_goals first
    | exact numeric_executable_opcode (by assumption)
    | exact memory_executable_opcode (by assumption)

set_option maxHeartbeats 2000000 in
theorem sign_executable_opcode {opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation) : ExecutableOpcode opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq,reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals simp_all [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode,floatBaseOpcodeValues]

theorem wasm2_immediate_executable_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) : ExecutableOpcode opcode := by
  cases encoded with
  | block _ | loop _ | if_ _ | else_ | end_ => simp [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode,floatBaseOpcodeValues]
  | plain encoded => exact wasm1_immediate_executable_opcode encoded
  | signExtension _ _ meaning => exact sign_executable_opcode meaning
  | saturating _ _ meaning _ => simp [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode]
  | reference encoded => cases encoded <;> simp [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode]
  | bulk _ _ encoded => simp [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode]
  | simd _ _ encoded => simp [ExecutableOpcode]
end Exec.Code

namespace Itasca.Wasm1
theorem At.executable_opcode {data start token next}
    (encoded : At data start token next) (inbounds : start.val < data.length) :
    Exec.Code.ExecutableOpcode data.val[start.val] := by
  obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm1_immediate_executable_opcode grammar
theorem BodyEncoding.next_executable_opcode {data body tokens position}
    (encoded : BodyEncoding data body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.ExecutableOpcode data.val[position.val] := by
  obtain ⟨token,next,atToken,allowed⟩ := encoded.next_executable_token
    (Exec.Code.SourceExecutable.body_wasm1 encoded) before remaining
  exact atToken.executable_opcode remaining
end Itasca.Wasm1

namespace Itasca.Wasm2
theorem At.executable_opcode {data start token next}
    (encoded : At data start token next) (inbounds : start.val < data.length) :
    Exec.Code.ExecutableOpcode data.val[start.val] := by
  obtain ⟨bytes,⟨opcode,immediate,rfl,grammar⟩,span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds,List.cons_append,List.head?_cons,Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm2_immediate_executable_opcode grammar

theorem BodyEncoding.next_executable_opcode {data body tokens position}
    (encoded : BodyEncoding data body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.ExecutableOpcode data.val[position.val] := by
  obtain ⟨token,next,atToken,allowed⟩ := encoded.next_executable_token (Exec.Code.SourceExecutable.body_wasm2 encoded) before remaining
  exact atToken.executable_opcode remaining
end Itasca.Wasm2
