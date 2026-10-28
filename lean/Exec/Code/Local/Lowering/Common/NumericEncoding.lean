import Exec.Code.Local.Lowering.Common.NumericOpcode
import Itasca.Spec.DeclaredReferences
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- All scalar integer numeric opcode bytes. -/
def integerOpcodes : List U8 :=
  [106#u8, 107#u8, 108#u8, 109#u8, 110#u8, 111#u8, 112#u8, 113#u8, 114#u8, 115#u8, 116#u8, 117#u8, 118#u8, 119#u8, 120#u8, 124#u8, 125#u8, 126#u8, 127#u8, 128#u8, 129#u8, 130#u8, 131#u8, 132#u8, 133#u8, 134#u8, 135#u8, 136#u8, 137#u8, 138#u8, 70#u8, 71#u8, 72#u8, 73#u8, 74#u8, 75#u8, 76#u8, 77#u8, 78#u8, 79#u8, 81#u8, 82#u8, 83#u8, 84#u8, 85#u8, 86#u8, 87#u8, 88#u8, 89#u8, 90#u8, 103#u8, 104#u8, 105#u8, 192#u8, 193#u8, 121#u8, 122#u8, 123#u8, 194#u8, 195#u8, 196#u8, 69#u8, 80#u8, 167#u8, 173#u8, 172#u8]

theorem integer_opcode_of_mem {opcode : U8} (member : opcode ∈ integerOpcodes) :
    ∃ op : Abs.Numeric.Instruction, UScalar.cast .U8 (integerOpcode op) = opcode := by
  simp only [integerOpcodes, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.binary .I32 (.ADD), rfl⟩
  · exact ⟨.binary .I32 (.SUB), rfl⟩
  · exact ⟨.binary .I32 (.MUL), rfl⟩
  · exact ⟨.binary .I32 (.DIV .S), rfl⟩
  · exact ⟨.binary .I32 (.DIV .U), rfl⟩
  · exact ⟨.binary .I32 (.REM .S), rfl⟩
  · exact ⟨.binary .I32 (.REM .U), rfl⟩
  · exact ⟨.binary .I32 (.AND), rfl⟩
  · exact ⟨.binary .I32 (.OR), rfl⟩
  · exact ⟨.binary .I32 (.XOR), rfl⟩
  · exact ⟨.binary .I32 (.SHL), rfl⟩
  · exact ⟨.binary .I32 (.SHR .S), rfl⟩
  · exact ⟨.binary .I32 (.SHR .U), rfl⟩
  · exact ⟨.binary .I32 (.ROTL), rfl⟩
  · exact ⟨.binary .I32 (.ROTR), rfl⟩
  · exact ⟨.binary .I64 (.ADD), rfl⟩
  · exact ⟨.binary .I64 (.SUB), rfl⟩
  · exact ⟨.binary .I64 (.MUL), rfl⟩
  · exact ⟨.binary .I64 (.DIV .S), rfl⟩
  · exact ⟨.binary .I64 (.DIV .U), rfl⟩
  · exact ⟨.binary .I64 (.REM .S), rfl⟩
  · exact ⟨.binary .I64 (.REM .U), rfl⟩
  · exact ⟨.binary .I64 (.AND), rfl⟩
  · exact ⟨.binary .I64 (.OR), rfl⟩
  · exact ⟨.binary .I64 (.XOR), rfl⟩
  · exact ⟨.binary .I64 (.SHL), rfl⟩
  · exact ⟨.binary .I64 (.SHR .S), rfl⟩
  · exact ⟨.binary .I64 (.SHR .U), rfl⟩
  · exact ⟨.binary .I64 (.ROTL), rfl⟩
  · exact ⟨.binary .I64 (.ROTR), rfl⟩
  · exact ⟨.compare .I32 (.EQ), rfl⟩
  · exact ⟨.compare .I32 (.NE), rfl⟩
  · exact ⟨.compare .I32 (.LT .S), rfl⟩
  · exact ⟨.compare .I32 (.LT .U), rfl⟩
  · exact ⟨.compare .I32 (.GT .S), rfl⟩
  · exact ⟨.compare .I32 (.GT .U), rfl⟩
  · exact ⟨.compare .I32 (.LE .S), rfl⟩
  · exact ⟨.compare .I32 (.LE .U), rfl⟩
  · exact ⟨.compare .I32 (.GE .S), rfl⟩
  · exact ⟨.compare .I32 (.GE .U), rfl⟩
  · exact ⟨.compare .I64 (.EQ), rfl⟩
  · exact ⟨.compare .I64 (.NE), rfl⟩
  · exact ⟨.compare .I64 (.LT .S), rfl⟩
  · exact ⟨.compare .I64 (.LT .U), rfl⟩
  · exact ⟨.compare .I64 (.GT .S), rfl⟩
  · exact ⟨.compare .I64 (.GT .U), rfl⟩
  · exact ⟨.compare .I64 (.LE .S), rfl⟩
  · exact ⟨.compare .I64 (.LE .U), rfl⟩
  · exact ⟨.compare .I64 (.GE .S), rfl⟩
  · exact ⟨.compare .I64 (.GE .U), rfl⟩
  · exact ⟨.unary .I32 .clz, rfl⟩
  · exact ⟨.unary .I32 .ctz, rfl⟩
  · exact ⟨.unary .I32 .popcnt, rfl⟩
  · exact ⟨.unary .I32 .extend8, rfl⟩
  · exact ⟨.unary .I32 .extend16, rfl⟩
  · exact ⟨.unary .I64 .clz, rfl⟩
  · exact ⟨.unary .I64 .ctz, rfl⟩
  · exact ⟨.unary .I64 .popcnt, rfl⟩
  · exact ⟨.unary .I64 .extend8, rfl⟩
  · exact ⟨.unary .I64 .extend16, rfl⟩
  · exact ⟨.unary .I64 .extend32, rfl⟩
  · exact ⟨.eqz .I32, rfl⟩
  · exact ⟨.eqz .I64, rfl⟩
  · exact ⟨.conversion .wrap, rfl⟩
  · exact ⟨.conversion .extendUnsigned, rfl⟩
  · exact ⟨.conversion .extendSigned, rfl⟩

theorem integer_source_declared (op : Abs.Numeric.Instruction) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.source := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> simp [Abs.Numeric.Instruction.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | compare ty operator => cases ty <;> cases operator <;> simp [Abs.Numeric.Instruction.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | unary ty operator => cases ty <;> cases operator <;> simp [Abs.Numeric.Instruction.source, Abs.Numeric.UnaryOperator.operation, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | eqz ty => cases ty <;> simp [Abs.Numeric.Instruction.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  | conversion operator => cases operator <;> simp [Abs.Numeric.Instruction.source, Abs.Numeric.Conversion.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Itasca.Runtime.Code
