import Itasca.Runtime.Code.Local.Lowering.Simd.SimdPureSignature
import Itasca.Runtime.Abs.Simd.Source
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

def simdLaneOutput (op : LaneOperation) : valtype :=
  if op.replace then .V128 else valtype_numtype op.scalar

theorem lane_source_signature (op : LaneOperation) (lane : laneidx) :
    Abs.Simd.PureSignature (op.instruction lane) op.inputs (simdLaneOutput op) := by
  cases op <;> with_unfolding_all constructor

theorem memory_source_signature (op : MemoryOperation) (argument : memarg) (lane : laneidx) :
    Abs.Simd.MemorySignature (op.instruction argument lane) op.inputs op.outputs := by
  cases op <;> with_unfolding_all constructor

theorem SimdImmediateMeaning.allowed {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) : Abs.SimdInstr source := by
  cases meaning with
  | pure opcode immediate op meaning => exact .pure (pure_source_signature meaning)
  | lane opcode immediate op meaning lane position => exact .pure (lane_source_signature op _)
  | memory opcode immediate op meaning argument lane memory available offset position =>
    exact .memory (memory_source_signature op argument _)
  | shuffle immediate low high bits => with_unfolding_all exact Abs.SimdInstr.pure (.shuffle _ _)

theorem SimdEmission.allowed {immediates constants C before source code after}
    (emission : SimdEmission immediates constants C before source code after) : Abs.SimdInstr source := by
  cases emission with
  | instruction front input output source opcode operand entry immediate instruction meaning metadata made position =>
    exact meaning.allowed
  | constant => exact .constant _
end Itasca.Runtime.Code
