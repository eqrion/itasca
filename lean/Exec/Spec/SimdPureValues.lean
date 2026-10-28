import Exec.Spec.SimdShape
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

/-- Source values represented by SIMD operand bits. SIMD uses only numerical
and vector types; reference cases retain a total definition. -/
def valueOfBits (ty : valtype) (bits : BitVec 128) : val :=
  match ty with
  | .I32 => .CONST .I32 (.mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat))
  | .I64 => .CONST .I64 (.mk_num__0 .I64 (.mk_uN (bits.setWidth 64).toNat))
  | .F32 => .CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (bits.setWidth 32).toNat))
  | .F64 => .CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 (bits.setWidth 64).toNat))
  | .V128 => .VCONST .V128 (.mk_uN bits.toNat)
  | .FUNCREF => .REF_NULL .FUNCREF
  | .EXTERNREF => .REF_NULL .EXTERNREF
  | .BOT => .REF_NULL .FUNCREF

/-- Up to three SIMD operands in their source order. -/
def operandValues (types : List valtype) (x y z : BitVec 128) : List val :=
  List.zipWith valueOfBits types [x,y,z]

end Itasca.Runtime.Spec.Simd
