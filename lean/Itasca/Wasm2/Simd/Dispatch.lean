import Itasca.Wasm2.Simd.ReadersTotal
import Itasca.Visitor.Basic
import Itasca.Wasm2.Simd.Tables

/-!
# Dispatch of SIMD instructions

`Simd.prefixStep` and `Simd.subStep` unfold the extracted `code.step_simd` (opcode `0xFD`) into
`CoreVisitor.run` applied to the reader for each operation class. `code.step_simd.eq_runs` proves
the two equal, and the `subStep.*` equations specialize it to pure, lane, memory, memory lane,
constant and shuffle subopcodes using the table agreement of `Wasm2/Simd/Tables`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Factorization of the SIMD subopcode dispatcher around its readers and visitor callbacks. -/
def subStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (subopcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let sig ← code.simd_signature subopcode
  match sig with
  | some sig =>
    CoreVisitor.run (code.read_simd_signature st sig)
      (fun v s _ => visitor.on_simd v s subopcode) v
  | none =>
    let lane ← code.simd_lane_info subopcode
    match lane with
    | some (ty, count, replace) =>
      CoreVisitor.run (code.read_simd_lane st data ty count replace)
        (fun v s lane => visitor.on_simd_lane v s subopcode lane) v
    | none =>
      let memory ← code.simd_memory_info subopcode
      match memory with
      | some (align, store, count) =>
        if count != 0#u8 then
          CoreVisitor.run (code.read_simd_memory_lane st data env align store count)
            (fun v s a => visitor.on_simd_memory_lane v s subopcode a.1 a.2) v
        else if store then
          CoreVisitor.run (code.read_store st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
        else
          CoreVisitor.run (code.read_load st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
      | none =>
        match subopcode with
        | 12#uscalar =>
          CoreVisitor.run (code.read_simd_const st data)
            (fun v s a => visitor.on_simd_const v s a.1 a.2) v
        | 13#uscalar =>
          CoreVisitor.run (code.read_simd_shuffle st data)
            (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v
        | _ => .ok (.Err .UnrecognizedOpcode, st, v)

/-- Reads the subopcode after `0xFD` and continues with `subStep`. -/
def prefixStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let r ← reader.read_u32_leb data st.pos
  match r with
  | .Err e => .ok (.Err e, st, v)
  | .Ok (subopcode, next) => subStep visitor {st with pos := next} data env subopcode v

end Itasca.Wasm2.Simd

namespace Itasca

theorem code.step_wasm2.simd {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 0xFD#u8 v = code.step_simd visitor st data env v := rfl

macro "finish_simd_run" : tactic => `(tactic| (
  simp only [CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨reply, w⟩ := pair
  all_goals cases reply <;> simp [code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
))

/-- `code.step_simd` equals its unfolded form `Wasm2.Simd.prefixStep`. -/
theorem code.step_simd.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (v : V) :
    code.step_simd visitor st data env v = Wasm2.Simd.prefixStep visitor st data env v := by
  unfold code.step_simd Wasm2.Simd.prefixStep
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Wasm2.Simd.subStep]
    congr 1
    funext sig
    cases sig with
    | some sig => finish_simd_run
    | none =>
      simp only
      congr 1
      funext lane
      cases lane with
      | some triple =>
        obtain ⟨ty, count, replace⟩ := triple
        finish_simd_run
      | none =>
        simp only
        congr 1
        funext mem
        cases mem with
        | some triple =>
          obtain ⟨align, store, count⟩ := triple
          simp only
          split
          · finish_simd_run
          · split <;> finish_simd_run
        | none =>
          simp only
          split
          · finish_simd_run
          · finish_simd_run
          · split <;> simp_all

end Itasca

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

theorem subStep.pure {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : Operation)
    (h : pureMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = CoreVisitor.run (code.read_simd_signature st op.signature.runtime)
      (fun v s _ => visitor.on_simd v s opcode) v := by
  simp only [subStep, pure_table, h, Option.map_some, bind_ok]

theorem subStep.lane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : LaneOperation)
    (h : laneMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (code.read_simd_lane st data op.runtime.1 op.runtime.2.1 op.replace)
      (fun v s a => visitor.on_simd_lane v s opcode a) v := by
  simp only [subStep, pure_table, lane_pure_none h, lane_table, h, Option.map_none,
    Option.map_some, bind_ok, LaneOperation.runtime]

theorem subStep.memory {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount = 0) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (if op.store then code.read_store st data env .V128 op.runtime.1
        else code.read_load st data env .V128 op.runtime.1)
      (fun v s a => visitor.on_simd_memory v s opcode a) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime, hc]
  cases op.store <;> rfl

theorem subStep.memoryLane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : MemoryOperation)
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
    (data : Slice U8) (env : metadata.Env) (v : V) :
    subStep visitor st data env 12#u32 v = CoreVisitor.run (code.read_simd_const st data)
      (fun v s a => visitor.on_simd_const v s a.1 a.2) v := by
  have hp : pureMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (12#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

theorem subStep.shuffle {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (v : V) :
    subStep visitor st data env 13#u32 v = CoreVisitor.run (code.read_simd_shuffle st data)
      (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v := by
  have hp : pureMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (13#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

end Itasca.Wasm2.Simd
