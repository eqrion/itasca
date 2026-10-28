import Itasca.Runtime.Interp.Simd.Common.SimdLaneRelation
import Itasca.Runtime.Interp.Simd.Common.SimdShuffleRelation
import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryTransition
import Itasca.Runtime.Abs.Simd.Transition
import Itasca.Runtime.Interp.Control.StructuredPoint
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt Itasca.Wasm2.Simd

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
end Itasca.Runtime.Interp.Simd
