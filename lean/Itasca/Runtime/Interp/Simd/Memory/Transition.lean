import Itasca.Runtime.Interp.Simd.Memory.Relation
import Itasca.Runtime.SourceMachine.Simd.MemoryTransition

/-!
Decoded memory changes and typed SIMD source results.

Main declarations: `MemoryBufferChange.source_change` and `memory_result_types`. A direct consumer is `Interp.Simd.Memory.SourceExecute`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem MemoryBufferChange.source_change {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : SourceMachine.Simd.MemoryChange s f sourceAfter := by
  cases change with
  | unchanged => exact .same
  | write start payload after inside payloadWf written => exact .write start payload payloadWf

theorem memory_result_types (op : MemoryOperation) (value : BitVec 128) :
    (Spec.Simd.operandValues op.outputs value 0 0).map SourceMachine.valueType = op.outputs := by
  cases op <;> rfl

end Itasca.Runtime.Interp.Simd
