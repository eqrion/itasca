import Exec.Abs.BinaryInstr
import Itasca.Binary.Wasm2.Encoding
namespace Exec.Code.SourceExecutable
open Aeneas Aeneas.Std Itasca

theorem integer (op : Abs.Numeric.Instruction) : Abs.BinaryInstr op.source := .numeric op
theorem floating (op : Abs.Float.Instruction) : Abs.BinaryInstr op.source := .float op

theorem numeric {opcode operation} (meaning : Numeric.opcodeMeaning opcode = some operation) :
    Abs.BinaryInstr operation.instruction := by
  unfold Numeric.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact integer (.eqz .I32)
  · exact integer (.compare .I32 (.EQ))
  · exact integer (.compare .I32 (.NE))
  · exact integer (.compare .I32 (.LT .S))
  · exact integer (.compare .I32 (.LT .U))
  · exact integer (.compare .I32 (.GT .S))
  · exact integer (.compare .I32 (.GT .U))
  · exact integer (.compare .I32 (.LE .S))
  · exact integer (.compare .I32 (.LE .U))
  · exact integer (.compare .I32 (.GE .S))
  · exact integer (.compare .I32 (.GE .U))
  · exact integer (.eqz .I64)
  · exact integer (.compare .I64 (.EQ))
  · exact integer (.compare .I64 (.NE))
  · exact integer (.compare .I64 (.LT .S))
  · exact integer (.compare .I64 (.LT .U))
  · exact integer (.compare .I64 (.GT .S))
  · exact integer (.compare .I64 (.GT .U))
  · exact integer (.compare .I64 (.LE .S))
  · exact integer (.compare .I64 (.LE .U))
  · exact integer (.compare .I64 (.GE .S))
  · exact integer (.compare .I64 (.GE .U))
  · exact floating (.compare .F32 .EQ)
  · exact floating (.compare .F32 .NE)
  · exact floating (.compare .F32 .LT)
  · exact floating (.compare .F32 .GT)
  · exact floating (.compare .F32 .LE)
  · exact floating (.compare .F32 .GE)
  · exact floating (.compare .F64 .EQ)
  · exact floating (.compare .F64 .NE)
  · exact floating (.compare .F64 .LT)
  · exact floating (.compare .F64 .GT)
  · exact floating (.compare .F64 .LE)
  · exact floating (.compare .F64 .GE)
  · exact integer (.unary .I32 .clz)
  · exact integer (.unary .I32 .ctz)
  · exact integer (.unary .I32 .popcnt)
  · exact integer (.binary .I32 (.ADD))
  · exact integer (.binary .I32 (.SUB))
  · exact integer (.binary .I32 (.MUL))
  · exact integer (.binary .I32 (.DIV .S))
  · exact integer (.binary .I32 (.DIV .U))
  · exact integer (.binary .I32 (.REM .S))
  · exact integer (.binary .I32 (.REM .U))
  · exact integer (.binary .I32 (.AND))
  · exact integer (.binary .I32 (.OR))
  · exact integer (.binary .I32 (.XOR))
  · exact integer (.binary .I32 (.SHL))
  · exact integer (.binary .I32 (.SHR .S))
  · exact integer (.binary .I32 (.SHR .U))
  · exact integer (.binary .I32 (.ROTL))
  · exact integer (.binary .I32 (.ROTR))
  · exact integer (.unary .I64 .clz)
  · exact integer (.unary .I64 .ctz)
  · exact integer (.unary .I64 .popcnt)
  · exact integer (.binary .I64 (.ADD))
  · exact integer (.binary .I64 (.SUB))
  · exact integer (.binary .I64 (.MUL))
  · exact integer (.binary .I64 (.DIV .S))
  · exact integer (.binary .I64 (.DIV .U))
  · exact integer (.binary .I64 (.REM .S))
  · exact integer (.binary .I64 (.REM .U))
  · exact integer (.binary .I64 (.AND))
  · exact integer (.binary .I64 (.OR))
  · exact integer (.binary .I64 (.XOR))
  · exact integer (.binary .I64 (.SHL))
  · exact integer (.binary .I64 (.SHR .S))
  · exact integer (.binary .I64 (.SHR .U))
  · exact integer (.binary .I64 (.ROTL))
  · exact integer (.binary .I64 (.ROTR))
  · exact floating (.unary .F32 .ABS)
  · exact floating (.unary .F32 .NEG)
  · exact floating (.unary .F32 .CEIL)
  · exact floating (.unary .F32 .FLOOR)
  · exact floating (.unary .F32 .TRUNC)
  · exact floating (.unary .F32 .NEAREST)
  · exact floating (.unary .F32 .SQRT)
  · exact floating (.binary .F32 .ADD)
  · exact floating (.binary .F32 .SUB)
  · exact floating (.binary .F32 .MUL)
  · exact floating (.binary .F32 .DIV)
  · exact floating (.binary .F32 .MIN)
  · exact floating (.binary .F32 .MAX)
  · exact floating (.binary .F32 .COPYSIGN)
  · exact floating (.unary .F64 .ABS)
  · exact floating (.unary .F64 .NEG)
  · exact floating (.unary .F64 .CEIL)
  · exact floating (.unary .F64 .FLOOR)
  · exact floating (.unary .F64 .TRUNC)
  · exact floating (.unary .F64 .NEAREST)
  · exact floating (.unary .F64 .SQRT)
  · exact floating (.binary .F64 .ADD)
  · exact floating (.binary .F64 .SUB)
  · exact floating (.binary .F64 .MUL)
  · exact floating (.binary .F64 .DIV)
  · exact floating (.binary .F64 .MIN)
  · exact floating (.binary .F64 .MAX)
  · exact floating (.binary .F64 .COPYSIGN)
  · exact integer (.conversion .wrap)
  · exact floating (.truncate .F32 .I32 .S false)
  · exact floating (.truncate .F32 .I32 .U false)
  · exact floating (.truncate .F64 .I32 .S false)
  · exact floating (.truncate .F64 .I32 .U false)
  · exact integer (.conversion .extendSigned)
  · exact integer (.conversion .extendUnsigned)
  · exact floating (.truncate .F32 .I64 .S false)
  · exact floating (.truncate .F32 .I64 .U false)
  · exact floating (.truncate .F64 .I64 .S false)
  · exact floating (.truncate .F64 .I64 .U false)
  · exact floating (.convert .I32 .F32 .S)
  · exact floating (.convert .I32 .F32 .U)
  · exact floating (.convert .I64 .F32 .S)
  · exact floating (.convert .I64 .F32 .U)
  · exact floating (.demote)
  · exact floating (.convert .I32 .F64 .S)
  · exact floating (.convert .I32 .F64 .U)
  · exact floating (.convert .I64 .F64 .S)
  · exact floating (.convert .I64 .F64 .U)
  · exact floating (.promote)
  · exact floating (.reinterpretFloat .F32)
  · exact floating (.reinterpretFloat .F64)
  · exact floating (.reinterpretInt .I32)
  · exact floating (.reinterpretInt .I64)

theorem sign {opcode operation} (meaning : Wasm2.NumericExtensions.signMeaning opcode = some operation) :
    Abs.BinaryInstr operation.instruction := by
  unfold Wasm2.NumericExtensions.signMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact integer (.unary .I32 .extend8)
  · exact integer (.unary .I32 .extend16)
  · exact integer (.unary .I64 .extend8)
  · exact integer (.unary .I64 .extend16)
  · exact integer (.unary .I64 .extend32)

theorem saturating {opcode operation} (meaning : Wasm2.NumericExtensions.saturatingMeaning opcode = some operation) :
    Abs.BinaryInstr operation.instruction := by
  unfold Wasm2.NumericExtensions.saturatingMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact floating (.truncate .F32 .I32 .S true)
  · exact floating (.truncate .F32 .I32 .U true)
  · exact floating (.truncate .F64 .I32 .S true)
  · exact floating (.truncate .F64 .I32 .U true)
  · exact floating (.truncate .F32 .I64 .S true)
  · exact floating (.truncate .F32 .I64 .U true)
  · exact floating (.truncate .F64 .I64 .S true)
  · exact floating (.truncate .F64 .I64 .U true)

theorem memory {opcode operation} (arg : code.MemArg)
    (meaning : MemoryMeaning.opcodeMeaning opcode = some operation) :
    Abs.BinaryInstr (operation.op arg) := by
  unfold MemoryMeaning.opcodeMeaning at meaning
  split at meaning <;> simp only [Option.some.injEq, reduceCtorEq] at meaning <;> try contradiction
  all_goals subst operation
  · exact .load (.full .I32) _
  · exact .load (.full .I64) _
  · exact .load (.full .F32) _
  · exact .load (.full .F64) _
  · exact .load (.packed .I32 .byte .S) _
  · exact .load (.packed .I32 .byte .U) _
  · exact .load (.packed .I32 .half .S) _
  · exact .load (.packed .I32 .half .U) _
  · exact .load (.packed .I64 .byte .S) _
  · exact .load (.packed .I64 .byte .U) _
  · exact .load (.packed .I64 .half .S) _
  · exact .load (.packed .I64 .half .U) _
  · exact .load (.packed .I64 .word .S) _
  · exact .load (.packed .I64 .word .U) _
  · exact .store (.full .I32) _
  · exact .store (.full .I64) _
  · exact .store (.full .F32) _
  · exact .store (.full .F64) _
  · exact .store (.packed .I32 .byte) _
  · exact .store (.packed .I32 .half) _
  · exact .store (.packed .I64 .byte) _
  · exact .store (.packed .I64 .half) _
  · exact .store (.packed .I64 .word) _
end Exec.Code.SourceExecutable
