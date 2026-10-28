import Itasca.Runtime.Abs.Float.Descriptor
namespace Itasca.Runtime.Abs.Float

def decodeInstruction : instr → Option Instruction
  | .UNOP .F32 (.mk_unop__1 .F32 op) => some (.unary .F32 op)
  | .UNOP .F64 (.mk_unop__1 .F64 op) => some (.unary .F64 op)
  | .BINOP .F32 (.mk_binop__1 .F32 op) => some (.binary .F32 op)
  | .BINOP .F64 (.mk_binop__1 .F64 op) => some (.binary .F64 op)
  | .RELOP .F32 (.mk_relop__1 .F32 op) => some (.compare .F32 op)
  | .RELOP .F64 (.mk_relop__1 .F64 op) => some (.compare .F64 op)
  | .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 (.CONVERT sign)) => some (.convert .I32 .F32 sign)
  | .CVTOP .F32 .I64 (.mk_cvtop___1 .I64 .F32 (.CONVERT sign)) => some (.convert .I64 .F32 sign)
  | .CVTOP .F64 .I32 (.mk_cvtop___1 .I32 .F64 (.CONVERT sign)) => some (.convert .I32 .F64 sign)
  | .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 (.CONVERT sign)) => some (.convert .I64 .F64 sign)
  | .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC sign)) => some (.truncate .F32 .I32 sign false)
  | .CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC sign)) => some (.truncate .F64 .I32 sign false)
  | .CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC sign)) => some (.truncate .F32 .I64 sign false)
  | .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC sign)) => some (.truncate .F64 .I64 sign false)
  | .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT sign)) => some (.truncate .F32 .I32 sign true)
  | .CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT sign)) => some (.truncate .F64 .I32 sign true)
  | .CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT sign)) => some (.truncate .F32 .I64 sign true)
  | .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT sign)) => some (.truncate .F64 .I64 sign true)
  | .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET) => some (.reinterpretFloat .F32)
  | .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET) => some (.reinterpretFloat .F64)
  | .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET) => some (.reinterpretInt .I32)
  | .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET) => some (.reinterpretInt .I64)
  | .CVTOP .F64 .F32 (.mk_cvtop___3 .F32 .F64 .PROMOTE) => some .promote
  | .CVTOP .F32 .F64 (.mk_cvtop___3 .F64 .F32 .DEMOTE) => some .demote
  | _ => none

@[simp] theorem decodeInstruction_source (op : Instruction) : decodeInstruction op.source = some op := by
  cases op with
  | unary ty op => cases ty <;> rfl
  | binary ty op => cases ty <;> rfl
  | compare ty op => cases ty <;> rfl
  | convert source target sign => cases source <;> cases target <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl

theorem Instruction.source_injective : Function.Injective Instruction.source := by
  intro left right same
  have := congrArg decodeInstruction same
  simpa only [decodeInstruction_source,Option.some.injEq] using this

end Itasca.Runtime.Abs.Float
