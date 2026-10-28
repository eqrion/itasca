import Itasca.Runtime.Abs.Numeric.Decode
import Itasca.Runtime.Abs.Float.Descriptor
import Itasca.Runtime.Abs.Memory.Descriptor
import Itasca.Runtime.Abs.Stateful.Descriptor
import Itasca.Runtime.Abs.Simd.Source
import Itasca.Runtime.Interp.Machines.Slice.SliceOpcode
import Itasca.Runtime.Interp.Control.NormalizeClosure

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- Source forms remaining after zero-byte normalization. -/
def ReadyInstruction : instr → Prop
  | .NOP | .DROP | .BLOCK _ _ => False
  | _ => True

/-- Ready source heads the interpreter dispatches, as recovered from the compiler certificate.
Indices and constant words come from emitted syntax, not assumptions. -/
inductive DispatchHead : instr → Prop where
  | numeric (op : Abs.Numeric.Instruction) : DispatchHead op.source
  | ordinary (op : OrdinaryOpcode) : DispatchHead op.source
  | loop (bt : blocktype) (body : List instr) : DispatchHead (.LOOP bt body)
  | call (index : U32) : DispatchHead (.CALL (.mk_uN index.val))
  | return_ : DispatchHead .RETURN
  | unreachable : DispatchHead .UNREACHABLE
  | float32 (bits : U32) : DispatchHead (.CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val)))
  | float64 (bits : U64) : DispatchHead (.CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val)))
  | select : DispatchHead (.SELECT none)
  | globalGet (index : U32) : DispatchHead (.GLOBAL_GET (.mk_uN index.val))
  | globalSet (index : U32) : DispatchHead (.GLOBAL_SET (.mk_uN index.val))
  | load (op : Abs.Memory.Load) (argument : memarg) : DispatchHead (op.source argument)
  | store (op : Abs.Memory.Store) (argument : memarg) : DispatchHead (op.source argument)
  | float (op : Abs.Float.Instruction) : DispatchHead op.source
  | stateful (op : Abs.Stateful.Instruction) : DispatchHead op.source
  | indirect (table type : U32) : DispatchHead (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val))
  | simd {op} : Abs.SimdInstr op → DispatchHead op
  | typedSelect (ty : valtype) : DispatchHead (.SELECT (some [ty]))
  | branchTable (depths : List labelidx) (fallback : labelidx) : DispatchHead (.BR_TABLE depths fallback)

end Itasca.Runtime.Interp
