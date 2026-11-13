import Itasca.Runtime.SourceMachine.Decode
import SpecExt.Builtins.Examples

/-!
Sections, each formerly its own module: Semantics, Decode.
-/

/-! ## Semantics -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt.Builtins

/-- Deterministic integer unary semantics at the source word width. -/
def unary (ty : Inn) (op : unop_Inn) (bits : BitVec (sizenn (numtype_Inn ty))) :
    BitVec (sizenn (numtype_Inn ty)) :=
  match op with
  | .CLZ => BitVec.ofNat _ (leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat))
  | .CTZ => BitVec.ofNat _ (leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse)
  | .POPCNT => BitVec.ofNat _ (population (integerBits (sizenn (numtype_Inn ty)) bits.toNat))
  | .EXTEND small => (bits.setWidth small).signExtend _


/-- Integer binary operations return no word precisely for a numeric trap. -/
def binary (ty : Inn) (op : binop_Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) : Option (BitVec (sizenn (numtype_Inn ty))) :=
  match op with
  | .ADD => some (a + b)
  | .SUB => some (a - b)
  | .MUL => some (a * b)
  | .DIV .U => if b.toNat = 0 then none else some (a / b)
  | .DIV .S => if b.toNat = 0 then none else
      if a = BitVec.intMin _ ∧ b = -1 then none else some (a.sdiv b)
  | .REM .U => if b.toNat = 0 then none else some (a % b)
  | .REM .S => if b.toNat = 0 then none else some (a.srem b)
  | .AND => some (a &&& b)
  | .OR => some (a ||| b)
  | .XOR => some (a ^^^ b)
  | .SHL => some (a <<< (b.toNat % sizenn (numtype_Inn ty)))
  | .SHR .U => some (a >>> (b.toNat % sizenn (numtype_Inn ty)))
  | .SHR .S => some (a.sshiftRight (b.toNat % sizenn (numtype_Inn ty)))
  | .ROTL => some (a.rotateLeft b.toNat)
  | .ROTR => some (a.rotateRight b.toNat)

/-- The optional word encodes SpecTec's empty trapping result or singleton value. -/
def binaryNumbers (ty : Inn) (result : Option (BitVec (sizenn (numtype_Inn ty)))) : List num_ :=
  match result with
  | none => []
  | some word => [.mk_num__0 ty (.mk_uN word.toNat)]


/-- Comparisons interpret operands at the declared signedness and produce i32. -/
def compare (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) : Nat :=
  match op with
  | .EQ => if a.toNat = b.toNat then 1 else 0
  | .NE => if a.toNat ≠ b.toNat then 1 else 0
  | .LT .U => if a.toNat < b.toNat then 1 else 0
  | .LT .S => if a.toInt < b.toInt then 1 else 0
  | .GT .U => if a.toNat > b.toNat then 1 else 0
  | .GT .S => if a.toInt > b.toInt then 1 else 0
  | .LE .U => if a.toNat ≤ b.toNat then 1 else 0
  | .LE .S => if a.toInt ≤ b.toInt then 1 else 0
  | .GE .U => if a.toNat ≥ b.toNat then 1 else 0
  | .GE .S => if a.toInt ≥ b.toInt then 1 else 0


/-- The three scalar integer width conversions, excluding float conversions. -/
inductive Conversion where
  | wrap | extendUnsigned | extendSigned

def Conversion.input : Conversion → Inn
  | .wrap => .I64
  | .extendUnsigned | .extendSigned => .I32

def Conversion.output : Conversion → Inn
  | .wrap => .I32
  | .extendUnsigned | .extendSigned => .I64

def Conversion.operator : Conversion → cvtop__
  | .wrap => .mk_cvtop___0 .I64 .I32 .WRAP
  | .extendUnsigned => .mk_cvtop___0 .I32 .I64 (.EXTEND .U)
  | .extendSigned => .mk_cvtop___0 .I32 .I64 (.EXTEND .S)

def Conversion.source (op : Conversion) : instr :=
  .CVTOP (numtype_Inn op.output) (numtype_Inn op.input) op.operator

def Conversion.apply (op : Conversion) : BitVec (sizenn (numtype_Inn op.input)) →
    BitVec (sizenn (numtype_Inn op.output)) :=
  match op with
  | .wrap => fun bits => bits.setWidth 32
  | .extendUnsigned => fun bits => bits.setWidth 64
  | .extendSigned => fun bits => bits.signExtend 64


/-- Exactly the integer unary instructions with scalar binary encodings. -/
inductive UnaryOperator : Inn → Type where
  | clz {ty} : UnaryOperator ty
  | ctz {ty} : UnaryOperator ty
  | popcnt {ty} : UnaryOperator ty
  | extend8 {ty} : UnaryOperator ty
  | extend16 {ty} : UnaryOperator ty
  | extend32 : UnaryOperator .I64

def UnaryOperator.operation {ty : Inn} : UnaryOperator ty → unop_Inn
  | .clz => .CLZ
  | .ctz => .CTZ
  | .popcnt => .POPCNT
  | .extend8 => .EXTEND 8
  | .extend16 => .EXTEND 16
  | .extend32 => .EXTEND 32

def UnaryOperator.opcode {ty : Inn} (op : UnaryOperator ty) : Nat :=
  match ty, op with
  | .I32, .clz => 103
  | .I32, .ctz => 104
  | .I32, .popcnt => 105
  | .I32, .extend8 => 192
  | .I32, .extend16 => 193
  | .I64, .clz => 121
  | .I64, .ctz => 122
  | .I64, .popcnt => 123
  | .I64, .extend8 => 194
  | .I64, .extend16 => 195
  | .I64, .extend32 => 196


/-- All scalar integer numeric instructions, indexed independently of the
interpreter and compiler bytecode representation. -/
inductive Instruction where
  | binary (ty : Inn) (op : binop_Inn)
  | unary (ty : Inn) (op : UnaryOperator ty)
  | compare (ty : Inn) (op : relop_Inn)
  | eqz (ty : Inn)
  | conversion (op : Conversion)

def Instruction.source : Instruction → instr
  | .binary ty op => .BINOP (numtype_Inn ty) (.mk_binop__0 ty op)
  | .unary ty op => .UNOP (numtype_Inn ty) (.mk_unop__0 ty op.operation)
  | .compare ty op => .RELOP (numtype_Inn ty) (.mk_relop__0 ty op)
  | .eqz ty => .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ)
  | .conversion op => op.source

def Instruction.input : Instruction → Inn
  | .binary ty _ | .unary ty _ | .compare ty _ | .eqz ty => ty
  | .conversion op => op.input

def Instruction.output : Instruction → Inn
  | .binary ty _ | .unary ty _ => ty
  | .compare _ _ | .eqz _ => .I32
  | .conversion op => op.output

def Instruction.arity : Instruction → Nat
  | .binary _ _ | .compare _ _ => 2
  | .unary _ _ | .eqz _ | .conversion _ => 1

/-- Unary instructions ignore the second operand, matching the slot handler's
uniform scalar interface. -/
def Instruction.apply (op : Instruction) :
    BitVec (sizenn (numtype_Inn op.input)) → BitVec (sizenn (numtype_Inn op.input)) →
    Option (BitVec (sizenn (numtype_Inn op.output))) :=
  match op with
  | .binary ty binop => Numeric.binary ty binop
  | .unary ty unop => fun a _ => some (Numeric.unary ty unop.operation a)
  | .compare ty relop => fun a b => some (BitVec.ofNat 32 (Numeric.compare ty relop a b))
  | .eqz _ => fun a _ => some (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0))
  | .conversion conv => fun a _ => some (conv.apply a)


end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Decode -/

section

namespace Itasca.Runtime.SourceMachine.Numeric

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

@[simp] theorem decode_instruction_source (op : Instruction) : decodeInstruction op.source = some op := by
  cases op with
  | binary ty op => cases ty <;> rfl
  | compare ty op => cases ty <;> rfl
  | eqz ty => cases ty <;> rfl
  | unary ty op => cases op <;> (try cases ty) <;> rfl
  | conversion op => cases op <;> rfl

end Itasca.Runtime.SourceMachine.Numeric

end
