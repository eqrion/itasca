import Exec.Abs.Float.Descriptor
import Exec.Generated.Equations
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def floatOpcode (op : Abs.Float.Instruction) : U16 :=
  UScalar.ofNat op.opcode (by have := op.opcode_bound; change op.opcode ≤ 65535; omega)

def floatInstruction (op : Abs.Float.Instruction) (dst a b : U32) : runtime.bytecode.Instr :=
  match op with
  | .unary .F32 .ABS => .F32Abs dst a b
  | .unary .F32 .NEG => .F32Neg dst a b
  | .unary .F32 .CEIL => .F32Ceil dst a b
  | .unary .F32 .FLOOR => .F32Floor dst a b
  | .unary .F32 .TRUNC => .F32Trunc dst a b
  | .unary .F32 .NEAREST => .F32Nearest dst a b
  | .unary .F32 .SQRT => .F32Sqrt dst a b
  | .unary .F64 .ABS => .F64Abs dst a b
  | .unary .F64 .NEG => .F64Neg dst a b
  | .unary .F64 .CEIL => .F64Ceil dst a b
  | .unary .F64 .FLOOR => .F64Floor dst a b
  | .unary .F64 .TRUNC => .F64Trunc dst a b
  | .unary .F64 .NEAREST => .F64Nearest dst a b
  | .unary .F64 .SQRT => .F64Sqrt dst a b
  | .binary .F32 .ADD => .F32Add dst a b
  | .binary .F32 .SUB => .F32Sub dst a b
  | .binary .F32 .MUL => .F32Mul dst a b
  | .binary .F32 .DIV => .F32Div dst a b
  | .binary .F32 .MIN => .F32Min dst a b
  | .binary .F32 .MAX => .F32Max dst a b
  | .binary .F32 .COPYSIGN => .F32Copysign dst a b
  | .binary .F64 .ADD => .F64Add dst a b
  | .binary .F64 .SUB => .F64Sub dst a b
  | .binary .F64 .MUL => .F64Mul dst a b
  | .binary .F64 .DIV => .F64Div dst a b
  | .binary .F64 .MIN => .F64Min dst a b
  | .binary .F64 .MAX => .F64Max dst a b
  | .binary .F64 .COPYSIGN => .F64Copysign dst a b
  | .compare .F32 .EQ => .F32Eq dst a b
  | .compare .F32 .NE => .F32Ne dst a b
  | .compare .F32 .LT => .F32Lt dst a b
  | .compare .F32 .GT => .F32Gt dst a b
  | .compare .F32 .LE => .F32Le dst a b
  | .compare .F32 .GE => .F32Ge dst a b
  | .compare .F64 .EQ => .F64Eq dst a b
  | .compare .F64 .NE => .F64Ne dst a b
  | .compare .F64 .LT => .F64Lt dst a b
  | .compare .F64 .GT => .F64Gt dst a b
  | .compare .F64 .LE => .F64Le dst a b
  | .compare .F64 .GE => .F64Ge dst a b
  | .convert .I32 .F32 .S => .F32ConvertI32S dst a b
  | .convert .I32 .F32 .U => .F32ConvertI32U dst a b
  | .convert .I32 .F64 .S => .F64ConvertI32S dst a b
  | .convert .I32 .F64 .U => .F64ConvertI32U dst a b
  | .convert .I64 .F32 .S => .F32ConvertI64S dst a b
  | .convert .I64 .F32 .U => .F32ConvertI64U dst a b
  | .convert .I64 .F64 .S => .F64ConvertI64S dst a b
  | .convert .I64 .F64 .U => .F64ConvertI64U dst a b
  | .truncate .F32 .I32 .S false => .I32TruncF32S dst a b
  | .truncate .F32 .I32 .S true => .I32TruncSatF32S dst a b
  | .truncate .F32 .I32 .U false => .I32TruncF32U dst a b
  | .truncate .F32 .I32 .U true => .I32TruncSatF32U dst a b
  | .truncate .F32 .I64 .S false => .I64TruncF32S dst a b
  | .truncate .F32 .I64 .S true => .I64TruncSatF32S dst a b
  | .truncate .F32 .I64 .U false => .I64TruncF32U dst a b
  | .truncate .F32 .I64 .U true => .I64TruncSatF32U dst a b
  | .truncate .F64 .I32 .S false => .I32TruncF64S dst a b
  | .truncate .F64 .I32 .S true => .I32TruncSatF64S dst a b
  | .truncate .F64 .I32 .U false => .I32TruncF64U dst a b
  | .truncate .F64 .I32 .U true => .I32TruncSatF64U dst a b
  | .truncate .F64 .I64 .S false => .I64TruncF64S dst a b
  | .truncate .F64 .I64 .S true => .I64TruncSatF64S dst a b
  | .truncate .F64 .I64 .U false => .I64TruncF64U dst a b
  | .truncate .F64 .I64 .U true => .I64TruncSatF64U dst a b
  | .reinterpretFloat .F32 => .I32ReinterpretF32 dst a b
  | .reinterpretFloat .F64 => .I64ReinterpretF64 dst a b
  | .reinterpretInt .I32 => .F32ReinterpretI32 dst a b
  | .reinterpretInt .I64 => .F64ReinterpretI64 dst a b
  | .promote => .F64PromoteF32 dst a b
  | .demote => .F32DemoteF64 dst a b

theorem floatInstruction_make (op : Abs.Float.Instruction) (dst a b : U32) :
    runtime.bytecode.Instr.make_scalar (floatOpcode op) dst a b =
      .ok (some (floatInstruction op dst a b)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl

theorem floatOpcode_binary (op : Abs.Float.Instruction) :
    runtime.compiler.lower.scalar_binary (floatOpcode op) = .ok (decide (op.arity = 2)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl
end Itasca.Runtime.Code
