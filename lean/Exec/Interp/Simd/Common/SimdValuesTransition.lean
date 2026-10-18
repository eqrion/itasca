import Exec.Interp.Simd.Common.SimdLaneRelation
import Exec.Interp.Simd.Common.SimdShuffleRelation
import Exec.Interp.Simd.Memory.SimdMemoryTransition
import Exec.Abs.Simd.Transition
import Exec.Interp.Control.StructuredPoint
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

theorem lane_value_type (op : LaneOperation) (value : BitVec 128) :
    Abs.valueType (laneResult op value) = if op.replace then .V128 else valtype_numtype op.scalar := by
  cases op <;> rfl

/-- A checked lane result attaches to the source frame without an additional
    result-typing or preservation premise. -/
theorem lane_values_transition (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (op : LaneOperation) (laneIndex : Nat) (front values : List val) (value : U128)
    (split : f.vals = front ++ values) (types : values.map Code.valueType = op.inputs)
    (effect : Step_pure (values.map admininstr_val ++ [admininstr_instr (op.instruction (.mk_uN laneIndex))])
      [admininstr_val (laneResult op value.bv)]) :
    Abs.Simd.Transition state f rest after (op.instruction (.mk_uN laneIndex)) op.inputs
      (if op.replace then .V128 else valtype_numtype op.scalar)
      ⟨state.store,state.ambient,{f with code := after,vals := front ++ [laneResult op value.bv]} :: rest,[]⟩ := by
  exact .next front values (laneResult op value.bv) split (by simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types) ⟨effect,lane_value_type op value.bv⟩

theorem shuffle_values_transition (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (low high : U64) (front values : List val) (value : U128)
    (split : f.vals = front ++ values) (types : values.map Code.valueType = [.V128,.V128])
    (effect : Step_pure (values.map admininstr_val ++ [admininstr_instr (shuffle low high)])
      [admininstr_val (Spec.Simd.valueOfBits .V128 value.bv)]) :
    Abs.Simd.Transition state f rest after (shuffle low high) [.V128,.V128] .V128
      ⟨state.store,state.ambient,{f with code := after,vals := front ++ [Spec.Simd.valueOfBits .V128 value.bv]} :: rest,[]⟩ := by
  exact .next front values (Spec.Simd.valueOfBits .V128 value.bv) split (by simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types) ⟨effect,rfl⟩

theorem memory_values_transition (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (op : MemoryOperation) (argument : memarg) (laneIndex : Nat)
    (front values : List val) (value : U128) (sourceAfter : store)
    (split : f.vals = front ++ values) (types : values.map Code.valueType = op.inputs)
    (change : Abs.Simd.MemoryChange state.store f.toFrame sourceAfter)
    (effect : StepH ⟨⟨state.store,f.toFrame⟩,
      values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]⟩ []
      ⟨⟨sourceAfter,f.toFrame⟩,(Spec.Simd.operandValues op.outputs value.bv 0 0).map admininstr_val⟩) :
    Abs.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs
      (.next ⟨sourceAfter,state.ambient,
        {f with code := after,vals := front ++ Spec.Simd.operandValues op.outputs value.bv 0 0} :: rest,[]⟩) := by
  exact .next front values (Spec.Simd.operandValues op.outputs value.bv 0 0) sourceAfter split (by simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types)
    (memory_result_types op value.bv) change effect

theorem memory_values_trap (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (op : MemoryOperation) (argument : memarg) (laneIndex : Nat) (front values : List val)
    (split : f.vals = front ++ values) (types : values.map Code.valueType = op.inputs)
    (effect : StepH ⟨⟨state.store,f.toFrame⟩,
      values.map admininstr_val ++ [admininstr_instr (op.instruction argument (.mk_uN laneIndex))]⟩ []
      ⟨⟨state.store,f.toFrame⟩,[.TRAP]⟩) :
    Abs.Simd.MemoryTransition state f rest after (op.instruction argument (.mk_uN laneIndex)) op.inputs op.outputs .trap := by
  exact .trap front values split (by simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types) effect
end Exec.Interp.Simd
