import Exec.Interp.Simd.Memory.SimdMemoryRelation
import Exec.Abs.Simd.MemoryTransition
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem MemoryBufferChange.source_change {s : store} {f : frame} {before after : Slice U8} {sourceAfter : store}
    (change : MemoryBufferChange s f before after sourceAfter) : Abs.Simd.MemoryChange s f sourceAfter := by
  cases change with
  | unchanged => exact .same
  | write start payload after inside payloadWf written => exact .write start payload payloadWf

theorem memory_operand_types (op : MemoryOperation) (x y z : BitVec 128) :
    (Spec.Simd.operandValues op.inputs x y z).map Abs.valueType = op.inputs := by
  cases op <;> rfl

theorem memory_result_types (op : MemoryOperation) (value : BitVec 128) :
    (Spec.Simd.operandValues op.outputs value 0 0).map Abs.valueType = op.outputs := by
  cases op <;> rfl

/-- Attach the exact concrete memory effect to the abstract SIMD transition. All
    operand and result types follow from the independently decoded operation. -/
theorem MemorySourceEffect.transition (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (x y z : BitVec 128) (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (beforeBytes afterBytes : Slice U8) (status : core.result.Result U128 runtime.ExecError)
    (values : f.vals = front ++ Spec.Simd.operandValues op.inputs x y z)
    (effect : MemorySourceEffect op argument laneIndex x y z state.store f.toFrame beforeBytes status afterBytes) :
    match status with
    | .Ok value => ∃ sourceAfter, MemoryBufferChange state.store f.toFrame beforeBytes afterBytes sourceAfter ∧
        Abs.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs
          (.next ⟨sourceAfter,state.ambient,
            {f with code := after, vals := front ++ Spec.Simd.operandValues op.outputs value.bv 0 0} :: rest,[]⟩)
    | .Err error => error = .Trap .MemoryOutOfBounds ∧ afterBytes = beforeBytes ∧
        Abs.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs .trap := by
  cases status with
  | Ok value =>
    obtain ⟨sourceAfter,change,step⟩ := effect
    refine ⟨sourceAfter,change,?_⟩
    exact .next front (Spec.Simd.operandValues op.inputs x y z)
      (Spec.Simd.operandValues op.outputs value.bv 0 0) sourceAfter values (memory_operand_types op x y z)
      (memory_result_types op value.bv) change.source_change step
  | Err error =>
    obtain ⟨errorEq,bytesEq,step⟩ := effect
    exact ⟨errorEq,bytesEq,.trap front (Spec.Simd.operandValues op.inputs x y z) values
      (memory_operand_types op x y z) step⟩
end Exec.Interp.Simd
