import Itasca.Wasm2.Simd.Dispatch
import Itasca.Wasm2.Simd.Tables

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Simd

theorem subStep.pure {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (opcode : U32) (v : V) (op : Operation)
    (h : pureMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = CoreVisitor.run (code.read_simd_signature st op.signature.runtime)
      (fun v s _ => visitor.on_simd v s opcode) v := by
  simp only [subStep, pure_table, h, Option.map_some, bind_ok]

theorem subStep.lane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (opcode : U32) (v : V) (op : LaneOperation)
    (h : laneMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (code.read_simd_lane st data op.runtime.1 op.runtime.2.1 op.replace)
      (fun v s a => visitor.on_simd_lane v s opcode a) v := by
  simp only [subStep, pure_table, lane_pure_none h, lane_table, h, Option.map_none,
    Option.map_some, bind_ok, LaneOperation.runtime]

theorem subStep.memory {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount = 0) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (if op.store then code.read_store st data env .V128 op.runtime.1
        else code.read_load st data env .V128 op.runtime.1)
      (fun v s a => visitor.on_simd_memory v s opcode a) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime, hc]
  cases op.store <;> rfl

theorem subStep.memoryLane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount ≠ 0) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (code.read_simd_memory_lane st data env op.runtime.1 op.store op.runtime.2.2)
      (fun v s a => visitor.on_simd_memory_lane v s opcode a.1 a.2) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime]
  have hn : (U8.ofNatCore op.laneCount (by cases op <;> decide) != 0#u8) = true := by
    cases op <;> first | contradiction | rfl
  rw [if_pos hn]

theorem subStep.constant {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (v : V) :
    subStep visitor st data env 12#u32 v = CoreVisitor.run (code.read_simd_const st data)
      (fun v s a => visitor.on_simd_const v s a.1 a.2) v := by
  have hp : pureMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (12#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

theorem subStep.shuffle {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (v : V) :
    subStep visitor st data env 13#u32 v = CoreVisitor.run (code.read_simd_shuffle st data)
      (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v := by
  have hp : pureMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (13#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

end Itasca.MultiValue.Simd
