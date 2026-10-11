import Itasca.MultiValue.SimdBinary

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Simd

def Signature.runtime : Signature → code.SimdSignature
  | .unary => .Unary
  | .binary => .Binary
  | .ternary => .Ternary
  | .test => .Test
  | .shift => .Shift
  | .splatI32 => .SplatI32
  | .splatI64 => .SplatI64
  | .splatF32 => .SplatF32
  | .splatF64 => .SplatF64

def LaneOperation.runtime (op : LaneOperation) : types.ValueType × U8 × Bool :=
  (match op.scalar with
   | .I32 => .I32 | .I64 => .I64 | .F32 => .F32 | .F64 => .F64,
   U8.ofNatCore op.count (by cases op <;> decide), op.replace)

def MemoryOperation.runtime (op : MemoryOperation) : U32 × Bool × U8 :=
  (U32.ofNatCore op.naturalAlign (by cases op <;> decide), op.store,
   U8.ofNatCore op.laneCount (by cases op <;> decide))

end Itasca.MultiValue.Simd
