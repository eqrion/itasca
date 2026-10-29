import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Float.Descriptor
import Itasca.Runtime.SourceMachine.Memory.Descriptor
import Itasca.Runtime.SourceMachine.Stateful.Descriptor
import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.Interp.Machine.Emission.Opcode
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
  | numeric (op : SourceMachine.Numeric.Instruction) : DispatchHead op.source
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
  | load (op : SourceMachine.Memory.Load) (argument : memarg) : DispatchHead (op.source argument)
  | store (op : SourceMachine.Memory.Store) (argument : memarg) : DispatchHead (op.source argument)
  | float (op : SourceMachine.Float.Instruction) : DispatchHead op.source
  | stateful (op : SourceMachine.Stateful.Instruction) : DispatchHead op.source
  | indirect (table type : U32) : DispatchHead (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val))
  | simd {op} : SourceMachine.SimdInstr op → DispatchHead op
  | typedSelect (ty : valtype) : DispatchHead (.SELECT (some [ty]))
  | branchTable (depths : List labelidx) (fallback : labelidx) : DispatchHead (.BR_TABLE depths fallback)

end Itasca.Runtime.Interp
