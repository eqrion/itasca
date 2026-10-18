import Exec.Code.Local.Control.Common.CumulativeOpcodes
import Exec.Code.Local.Lowering.Simd.SimdCumulativeTokens
import Exec.Abs.Simd.Exclusion
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open Aeneas Aeneas.Std Itasca
namespace Exec.Code

def SimdCumulativeOpcode (opcode : U8) : Prop := CumulativeOpcode opcode ∨ opcode = 253#u8

def SimdCumulativeHead (instruction : instr) : Bool := CumulativeHead instruction || Abs.simdSourceTag instruction

theorem simd_cumulative_head {instruction} (supported : Abs.SimdCumulativeInstr instruction) :
    SimdCumulativeHead instruction = true := by
  cases supported with
  | cumulative h => simp [SimdCumulativeHead,cumulative_head h]
  | simd h => simp [SimdCumulativeHead,h.source_tag]
  | _ => rfl
set_option maxHeartbeats 2000000 in
theorem numeric_simd_cumulative_opcode {opcode operation}
    (meaning : Numeric.opcodeMeaning opcode = some operation)
    (supported : Abs.SimdCumulativeInstr operation.instruction) : CumulativeOpcode opcode := by
  have head := simd_cumulative_head supported
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  all_goals first | solve | simp_all [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues] | contradiction
theorem memory_simd_cumulative_opcode {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (_supported : Abs.SimdCumulativeInstr (operation.op arg)) : CumulativeOpcode opcode := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]

theorem wasm1_immediate_simd_cumulative_opcode {opcode token bytes}
    (encoded : Wasm1.Immediate opcode token bytes) (supported : Wasm1.SimdCumulativeToken token) :
    CumulativeOpcode opcode := by
  cases encoded <;> try { simp [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues] }
  all_goals change Abs.SimdCumulativeInstr _ at supported
  all_goals first
    | exact numeric_simd_cumulative_opcode (by assumption) supported
    | exact memory_simd_cumulative_opcode _ (by assumption) supported
    | have head := simd_cumulative_head supported; contradiction

set_option maxHeartbeats 2000000 in
theorem sign_simd_cumulative_opcode {opcode operation}
    (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation)
    (_supported : Abs.SimdCumulativeInstr operation.instruction) : CumulativeOpcode opcode := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation; simp_all [CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]

theorem wasm2_immediate_simd_cumulative_opcode {opcode token bytes}
    (encoded : Wasm2.Immediate opcode token bytes) (supported : Wasm2.SimdCumulativeToken token) :
    SimdCumulativeOpcode opcode := by
  cases encoded with
  | block _ | loop _ | if_ _ | else_ | end_ => simp [SimdCumulativeOpcode, CumulativeOpcode, FloatCoreOpcode, CoreOpcode, SliceOpcode, floatBaseOpcodeValues]
  | plain encoded => exact .inl (wasm1_immediate_simd_cumulative_opcode encoded supported)
  | signExtension _ _ meaning => exact .inl (sign_simd_cumulative_opcode meaning supported)
  | saturating _ _ meaning _ => exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))
  | reference encoded =>
    cases encoded <;> first
      | solve | simp [SimdCumulativeOpcode, CumulativeOpcode]
      | have head := simd_cumulative_head supported; contradiction
  | bulk _ _ encoded => exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))
  | simd _ _ encoded => exact .inr rfl

end Exec.Code

namespace Itasca.Wasm2
/-- The actual next byte of a supported token selects one of the proved
scalar/control reader cases. -/
theorem At.simd_cumulative_opcode {data start token next}
    (encoded : At data start token next) (supported : SimdCumulativeToken token)
    (inbounds : start.val < data.length) :
    Exec.Code.SimdCumulativeOpcode data.val[start.val] := by
  obtain ⟨bytes, ⟨opcode, immediate, rfl, grammar⟩, span⟩ := encoded
  have head := congrArg List.head? span.suffix
  have equal : data.val[start.val] = opcode := by
    simpa only [List.drop_eq_getElem_cons inbounds, List.cons_append,
      List.head?_cons, Option.some.injEq] using head
  rw [equal]
  exact Exec.Code.wasm2_immediate_simd_cumulative_opcode grammar supported

/-- Source-core membership constrains opcode dispatch at every unfinished
canonical reader boundary. -/
theorem BodyEncoding.next_simd_cumulative_opcode {data body tokens position}
    (encoded : BodyEncoding data body) (supported : Forall Exec.Abs.SimdCumulativeInstr body)
    (before : Consumed data 0#usize tokens position) (remaining : position.val < data.length) :
    Exec.Code.SimdCumulativeOpcode data.val[position.val] := by
  obtain ⟨token, next, atToken, allowed⟩ := encoded.next_simd_cumulative_token supported before remaining
  exact atToken.simd_cumulative_opcode allowed remaining
end Itasca.Wasm2
