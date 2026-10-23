import Exec.Interp.Simd.Memory.SimdMemoryRelation
import Exec.Abs.Simd.MemoryTransition
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem MemoryBufferChange.source_change {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : Abs.Simd.MemoryChange s f sourceAfter := by
  cases change with
  | unchanged => exact .same
  | write start payload after inside payloadWf written => exact .write start payload payloadWf

theorem memory_result_types (op : MemoryOperation) (value : BitVec 128) :
    (Spec.Simd.operandValues op.outputs value 0 0).map Abs.valueType = op.outputs := by
  cases op <;> rfl

end Exec.Interp.Simd
