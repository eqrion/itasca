import Exec.Abs.Numeric.Semantics

namespace Exec.Abs.Numeric

/-- Recognize exactly the integer instruction descriptors, including matching
outer and inner source type tags. -/
def decodeInstruction : instr → Option Instruction
  | .BINOP .I32 (.mk_binop__0 .I32 op) => some (.binary .I32 op)
  | .BINOP .I64 (.mk_binop__0 .I64 op) => some (.binary .I64 op)
  | .RELOP .I32 (.mk_relop__0 .I32 op) => some (.compare .I32 op)
  | .RELOP .I64 (.mk_relop__0 .I64 op) => some (.compare .I64 op)
  | .TESTOP .I32 (.mk_testop__0 .I32 .EQZ) => some (.eqz .I32)
  | .TESTOP .I64 (.mk_testop__0 .I64 .EQZ) => some (.eqz .I64)
  | .UNOP .I32 (.mk_unop__0 .I32 .CLZ) => some (.unary .I32 .clz)
  | .UNOP .I32 (.mk_unop__0 .I32 .CTZ) => some (.unary .I32 .ctz)
  | .UNOP .I32 (.mk_unop__0 .I32 .POPCNT) => some (.unary .I32 .popcnt)
  | .UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 8)) => some (.unary .I32 .extend8)
  | .UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 16)) => some (.unary .I32 .extend16)
  | .UNOP .I64 (.mk_unop__0 .I64 .CLZ) => some (.unary .I64 .clz)
  | .UNOP .I64 (.mk_unop__0 .I64 .CTZ) => some (.unary .I64 .ctz)
  | .UNOP .I64 (.mk_unop__0 .I64 .POPCNT) => some (.unary .I64 .popcnt)
  | .UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 8)) => some (.unary .I64 .extend8)
  | .UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 16)) => some (.unary .I64 .extend16)
  | .UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 32)) => some (.unary .I64 .extend32)
  | .CVTOP .I32 .I64 (.mk_cvtop___0 .I64 .I32 .WRAP) => some (.conversion .wrap)
  | .CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)) => some (.conversion .extendUnsigned)
  | .CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .S)) => some (.conversion .extendSigned)
  | _ => none

@[simp] theorem decodeInstruction_source (op : Instruction) : decodeInstruction op.source = some op := by
  cases op with
  | binary ty op => cases ty <;> rfl
  | compare ty op => cases ty <;> rfl
  | eqz ty => cases ty <;> rfl
  | unary ty op => cases op <;> (try cases ty) <;> rfl
  | conversion op => cases op <;> rfl

end Exec.Abs.Numeric
