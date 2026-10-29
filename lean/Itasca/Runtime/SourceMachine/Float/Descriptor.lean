import Itasca.Runtime.SourceMachine.State
import SpecExt.Builtins.Float.Decoding

/-!
Scalar floating-point source instructions and their decoding. This cheap descriptor layer specifies types, opcodes and source syntax independently of transition correctness.
-/

/-! ## Descriptor -/

section

namespace Itasca.Runtime.SourceMachine.Float
open SpecExt SpecExt.Builtins SpecExt.Builtins.Float

/-- Scalar float syntax, independent of compiler bytecode and native operations. -/
inductive Instruction where
  | unary (ty : Fnn) (op : unop_Fnn)
  | binary (ty : Fnn) (op : binop_Fnn)
  | compare (ty : Fnn) (op : relop_Fnn)
  | convert (source : Inn) (target : Fnn) (sign : sx)
  | truncate (source : Fnn) (target : Inn) (sign : sx) (saturating : Bool)
  | reinterpretFloat (source : Fnn)
  | reinterpretInt (source : Inn)
  | promote
  | demote

def integerType : Fnn → Inn
  | .F32 => .I32
  | .F64 => .I64

def floatType : Inn → Fnn
  | .I32 => .F32
  | .I64 => .F64

def Instruction.input : Instruction → numtype
  | .unary ty _ | .binary ty _ | .compare ty _ => numtype_Fnn ty
  | .convert source _ _ | .reinterpretInt source => numtype_Inn source
  | .truncate source _ _ _ | .reinterpretFloat source => numtype_Fnn source
  | .promote => .F32
  | .demote => .F64

def Instruction.output : Instruction → numtype
  | .unary ty _ | .binary ty _ => numtype_Fnn ty
  | .compare _ _ => .I32
  | .convert _ target _ => numtype_Fnn target
  | .truncate _ target _ _ => numtype_Inn target
  | .reinterpretFloat source => numtype_Inn (integerType source)
  | .reinterpretInt source => numtype_Fnn (floatType source)
  | .promote => .F64
  | .demote => .F32

def Instruction.arity : Instruction → Nat
  | .binary _ _ | .compare _ _ => 2
  | _ => 1

def Instruction.source : Instruction → instr
  | .unary ty op => .UNOP (numtype_Fnn ty) (.mk_unop__1 ty op)
  | .binary ty op => .BINOP (numtype_Fnn ty) (.mk_binop__1 ty op)
  | .compare ty op => .RELOP (numtype_Fnn ty) (.mk_relop__1 ty op)
  | .convert source target sign => .CVTOP (numtype_Fnn target) (numtype_Inn source)
      (.mk_cvtop___1 source target (.CONVERT sign))
  | .truncate source target sign saturating => .CVTOP (numtype_Inn target) (numtype_Fnn source)
      (.mk_cvtop___2 source target (if saturating then .TRUNC_SAT sign else .TRUNC sign))
  | .reinterpretFloat source => .CVTOP (numtype_Inn (integerType source)) (numtype_Fnn source)
      (.mk_cvtop___2 source (integerType source) .REINTERPRET)
  | .reinterpretInt source => .CVTOP (numtype_Fnn (floatType source)) (numtype_Inn source)
      (.mk_cvtop___1 source (floatType source) .REINTERPRET)
  | .promote => .CVTOP .F64 .F32 (.mk_cvtop___3 .F32 .F64 .PROMOTE)
  | .demote => .CVTOP .F32 .F64 (.mk_cvtop___3 .F64 .F32 .DEMOTE)

def unaryIndex : unop_Fnn → Nat
  | .ABS => 0 | .NEG => 1 | .CEIL => 2 | .FLOOR => 3 | .TRUNC => 4 | .NEAREST => 5 | .SQRT => 6

def binaryIndex : binop_Fnn → Nat
  | .ADD => 0 | .SUB => 1 | .MUL => 2 | .DIV => 3 | .MIN => 4 | .MAX => 5 | .COPYSIGN => 6

def compareIndex : relop_Fnn → Nat
  | .EQ => 0 | .NE => 1 | .LT => 2 | .GT => 3 | .LE => 4 | .GE => 5

def signIndex : sx → Nat
  | .S => 0 | .U => 1

/-- Saturating conversions use the compiler's expanded scalar opcode space. -/
def Instruction.opcode : Instruction → Nat
  | .unary ty op => (match ty with | .F32 => 139 | .F64 => 153) + unaryIndex op
  | .binary ty op => (match ty with | .F32 => 146 | .F64 => 160) + binaryIndex op
  | .compare ty op => (match ty with | .F32 => 91 | .F64 => 97) + compareIndex op
  | .convert source target sign =>
      (match target with | .F32 => 178 | .F64 => 183) +
      (match source with | .I32 => 0 | .I64 => 2) + signIndex sign
  | .truncate source target sign saturating =>
      (if saturating then (match target with | .I32 => 256 | .I64 => 260)
        else (match target with | .I32 => 168 | .I64 => 174)) +
      (match source with | .F32 => 0 | .F64 => 2) + signIndex sign
  | .reinterpretFloat .F32 => 188
  | .reinterpretFloat .F64 => 189
  | .reinterpretInt .I32 => 190
  | .reinterpretInt .I64 => 191
  | .promote => 187
  | .demote => 182

/-- Canonical decoding of a scalar operand, preserving float payload bits. -/
def numberOfBits : numtype → Nat → num_
  | .I32, bits => .mk_num__0 .I32 (.mk_uN bits)
  | .I64, bits => .mk_num__0 .I64 (.mk_uN bits)
  | .F32, bits => .mk_num__1 .F32 (floatOfBits 32 bits)
  | .F64, bits => .mk_num__1 .F64 (floatOfBits 64 bits)

def Instruction.operands (op : Instruction) (a b : Nat) : List val :=
  if op.arity = 1 then [.CONST op.input (numberOfBits op.input a)]
  else [.CONST op.input (numberOfBits op.input a), .CONST op.input (numberOfBits op.input b)]

/-- The relation retains every source-permitted float result, including NaNs.
A missing result is a source numeric trap, not a host or allocation error. -/
def Instruction.Result (op : Instruction) (a b : Nat) (result : Option Nat) : Prop :=
  match result with
  | some bits => bits < 2^sizenn op.output ∧
      Step_pure (vals (op.operands a b) ++ [admininstr_instr op.source])
        [admininstr_val (.CONST op.output (numberOfBits op.output bits))]
  | none => Step_pure (vals (op.operands a b) ++ [admininstr_instr op.source]) [.TRAP]

theorem Instruction.arity_valid (op : Instruction) : op.arity = 1 ∨ op.arity = 2 := by
  cases op <;> simp [arity]

theorem Instruction.opcode_bound (op : Instruction) : op.opcode < 65536 := by
  cases op with
  | unary ty op => cases ty <;> cases op <;> decide
  | binary ty op => cases ty <;> cases op <;> decide
  | compare ty op => cases ty <;> cases op <;> decide
  | convert source target sign => cases source <;> cases target <;> cases sign <;> decide
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> decide
  | reinterpretFloat source => cases source <;> decide
  | reinterpretInt source => cases source <;> decide
  | promote | demote => decide



end Itasca.Runtime.SourceMachine.Float

end

/-! ## Decode -/

section

namespace Itasca.Runtime.SourceMachine.Float

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

@[simp] theorem decode_instruction_source (op : Instruction) : decodeInstruction op.source = some op := by
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
  simpa only [decode_instruction_source,Option.some.injEq] using this

end Itasca.Runtime.SourceMachine.Float

end
