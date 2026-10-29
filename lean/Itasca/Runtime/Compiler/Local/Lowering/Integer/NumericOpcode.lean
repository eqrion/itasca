import Itasca.Runtime.SourceMachine.Numeric.Semantics
import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Equations

/-!
Binary encodings of all scalar integer numeric instructions.

Main declarations: `integerOpcode` and `integerInstruction`. A direct consumer is `Compiler.Local.Lowering.Integer.NumericEncoding`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Abs.Numeric

/-- Binary encodings of all scalar integer numeric instructions. -/
def integerOpcode : Instruction → U16
  | .binary .I32 (.ADD) => 106#u16
  | .binary .I32 (.SUB) => 107#u16
  | .binary .I32 (.MUL) => 108#u16
  | .binary .I32 (.DIV .S) => 109#u16
  | .binary .I32 (.DIV .U) => 110#u16
  | .binary .I32 (.REM .S) => 111#u16
  | .binary .I32 (.REM .U) => 112#u16
  | .binary .I32 (.AND) => 113#u16
  | .binary .I32 (.OR) => 114#u16
  | .binary .I32 (.XOR) => 115#u16
  | .binary .I32 (.SHL) => 116#u16
  | .binary .I32 (.SHR .S) => 117#u16
  | .binary .I32 (.SHR .U) => 118#u16
  | .binary .I32 (.ROTL) => 119#u16
  | .binary .I32 (.ROTR) => 120#u16
  | .binary .I64 (.ADD) => 124#u16
  | .binary .I64 (.SUB) => 125#u16
  | .binary .I64 (.MUL) => 126#u16
  | .binary .I64 (.DIV .S) => 127#u16
  | .binary .I64 (.DIV .U) => 128#u16
  | .binary .I64 (.REM .S) => 129#u16
  | .binary .I64 (.REM .U) => 130#u16
  | .binary .I64 (.AND) => 131#u16
  | .binary .I64 (.OR) => 132#u16
  | .binary .I64 (.XOR) => 133#u16
  | .binary .I64 (.SHL) => 134#u16
  | .binary .I64 (.SHR .S) => 135#u16
  | .binary .I64 (.SHR .U) => 136#u16
  | .binary .I64 (.ROTL) => 137#u16
  | .binary .I64 (.ROTR) => 138#u16
  | .compare .I32 (.EQ) => 70#u16
  | .compare .I32 (.NE) => 71#u16
  | .compare .I32 (.LT .S) => 72#u16
  | .compare .I32 (.LT .U) => 73#u16
  | .compare .I32 (.GT .S) => 74#u16
  | .compare .I32 (.GT .U) => 75#u16
  | .compare .I32 (.LE .S) => 76#u16
  | .compare .I32 (.LE .U) => 77#u16
  | .compare .I32 (.GE .S) => 78#u16
  | .compare .I32 (.GE .U) => 79#u16
  | .compare .I64 (.EQ) => 81#u16
  | .compare .I64 (.NE) => 82#u16
  | .compare .I64 (.LT .S) => 83#u16
  | .compare .I64 (.LT .U) => 84#u16
  | .compare .I64 (.GT .S) => 85#u16
  | .compare .I64 (.GT .U) => 86#u16
  | .compare .I64 (.LE .S) => 87#u16
  | .compare .I64 (.LE .U) => 88#u16
  | .compare .I64 (.GE .S) => 89#u16
  | .compare .I64 (.GE .U) => 90#u16
  | .unary .I32 .clz => 103#u16
  | .unary .I32 .ctz => 104#u16
  | .unary .I32 .popcnt => 105#u16
  | .unary .I32 .extend8 => 192#u16
  | .unary .I32 .extend16 => 193#u16
  | .unary .I64 .clz => 121#u16
  | .unary .I64 .ctz => 122#u16
  | .unary .I64 .popcnt => 123#u16
  | .unary .I64 .extend8 => 194#u16
  | .unary .I64 .extend16 => 195#u16
  | .unary .I64 .extend32 => 196#u16
  | .eqz .I32 => 69#u16
  | .eqz .I64 => 80#u16
  | .conversion .wrap => 167#u16
  | .conversion .extendUnsigned => 173#u16
  | .conversion .extendSigned => 172#u16

/-- The exact scalar bytecode constructor used by compiler and interpreter. -/
def integerInstruction (op : Instruction) (dst a b : U32) : runtime.bytecode.Instr :=
  match op with
  | .binary .I32 (.ADD) => .I32Add dst a b
  | .binary .I32 (.SUB) => .I32Sub dst a b
  | .binary .I32 (.MUL) => .I32Mul dst a b
  | .binary .I32 (.DIV .S) => .I32DivS dst a b
  | .binary .I32 (.DIV .U) => .I32DivU dst a b
  | .binary .I32 (.REM .S) => .I32RemS dst a b
  | .binary .I32 (.REM .U) => .I32RemU dst a b
  | .binary .I32 (.AND) => .I32And dst a b
  | .binary .I32 (.OR) => .I32Or dst a b
  | .binary .I32 (.XOR) => .I32Xor dst a b
  | .binary .I32 (.SHL) => .I32Shl dst a b
  | .binary .I32 (.SHR .S) => .I32ShrS dst a b
  | .binary .I32 (.SHR .U) => .I32ShrU dst a b
  | .binary .I32 (.ROTL) => .I32Rotl dst a b
  | .binary .I32 (.ROTR) => .I32Rotr dst a b
  | .binary .I64 (.ADD) => .I64Add dst a b
  | .binary .I64 (.SUB) => .I64Sub dst a b
  | .binary .I64 (.MUL) => .I64Mul dst a b
  | .binary .I64 (.DIV .S) => .I64DivS dst a b
  | .binary .I64 (.DIV .U) => .I64DivU dst a b
  | .binary .I64 (.REM .S) => .I64RemS dst a b
  | .binary .I64 (.REM .U) => .I64RemU dst a b
  | .binary .I64 (.AND) => .I64And dst a b
  | .binary .I64 (.OR) => .I64Or dst a b
  | .binary .I64 (.XOR) => .I64Xor dst a b
  | .binary .I64 (.SHL) => .I64Shl dst a b
  | .binary .I64 (.SHR .S) => .I64ShrS dst a b
  | .binary .I64 (.SHR .U) => .I64ShrU dst a b
  | .binary .I64 (.ROTL) => .I64Rotl dst a b
  | .binary .I64 (.ROTR) => .I64Rotr dst a b
  | .compare .I32 (.EQ) => .I32Eq dst a b
  | .compare .I32 (.NE) => .I32Ne dst a b
  | .compare .I32 (.LT .S) => .I32LtS dst a b
  | .compare .I32 (.LT .U) => .I32LtU dst a b
  | .compare .I32 (.GT .S) => .I32GtS dst a b
  | .compare .I32 (.GT .U) => .I32GtU dst a b
  | .compare .I32 (.LE .S) => .I32LeS dst a b
  | .compare .I32 (.LE .U) => .I32LeU dst a b
  | .compare .I32 (.GE .S) => .I32GeS dst a b
  | .compare .I32 (.GE .U) => .I32GeU dst a b
  | .compare .I64 (.EQ) => .I64Eq dst a b
  | .compare .I64 (.NE) => .I64Ne dst a b
  | .compare .I64 (.LT .S) => .I64LtS dst a b
  | .compare .I64 (.LT .U) => .I64LtU dst a b
  | .compare .I64 (.GT .S) => .I64GtS dst a b
  | .compare .I64 (.GT .U) => .I64GtU dst a b
  | .compare .I64 (.LE .S) => .I64LeS dst a b
  | .compare .I64 (.LE .U) => .I64LeU dst a b
  | .compare .I64 (.GE .S) => .I64GeS dst a b
  | .compare .I64 (.GE .U) => .I64GeU dst a b
  | .unary .I32 .clz => .I32Clz dst a b
  | .unary .I32 .ctz => .I32Ctz dst a b
  | .unary .I32 .popcnt => .I32Popcnt dst a b
  | .unary .I32 .extend8 => .I32Extend8S dst a b
  | .unary .I32 .extend16 => .I32Extend16S dst a b
  | .unary .I64 .clz => .I64Clz dst a b
  | .unary .I64 .ctz => .I64Ctz dst a b
  | .unary .I64 .popcnt => .I64Popcnt dst a b
  | .unary .I64 .extend8 => .I64Extend8S dst a b
  | .unary .I64 .extend16 => .I64Extend16S dst a b
  | .unary .I64 .extend32 => .I64Extend32S dst a b
  | .eqz .I32 => .I32Eqz dst a b
  | .eqz .I64 => .I64Eqz dst a b
  | .conversion .wrap => .I32WrapI64 dst a b
  | .conversion .extendUnsigned => .I64ExtendI32U dst a b
  | .conversion .extendSigned => .I64ExtendI32S dst a b

theorem integerOpcode_byte (op : Instruction) : (integerOpcode op).val ≤ 255 := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> decide
  | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> decide
  | unary ty operator => cases ty <;> cases operator <;> decide
  | eqz ty => cases ty <;> decide
  | conversion operator => cases operator <;> decide

theorem integerInstruction_make (op : Instruction) (dst a b : U32) :
    runtime.bytecode.Instr.make_scalar (integerOpcode op) dst a b =
      .ok (some (integerInstruction op dst a b)) := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion operator => cases operator <;> rfl

theorem integerOpcode_binary (op : Instruction) :
    runtime.compiler.lower.scalar_binary (integerOpcode op) = .ok (decide (op.arity = 2)) := by
  cases op with
  | binary ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;> rfl
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion operator => cases operator <;> rfl
end Itasca.Runtime.Code
