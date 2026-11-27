import Itasca.Results.Definitions.Visitor
import Itasca.Visitor.Total
import Itasca.Binary.Scalar.Encoding
import Mathlib.Tactic.IntervalCases
import Itasca.Support.Translation
import ItascaRust.Types
import Itasca.Handler.ScalarCompleteness
import Itasca.Handler.ScalarOperations

/-!
Proofs for Visitor.

This module collects Events, RunTrace.
Each section documents its contracts and consumers.
-/

/-! ## Events -/

section

/-! ## Dispatch -/

section

/-!
# Step dispatch for control and constant instructions

For each control and constant opcode, `Visitor.Dispatch.dispatch_*` rewrites `code.step` at that opcode
to `Visitor.Core.run` of the instruction's reader and its visitor hook. `memory_fallback` shows
`code.step_memory` falls through to `code.step_numeric` for opcodes outside the memory table.
Covers the scalar step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Dispatch

/-- `code.step` on `code.OP_I32_CONST` runs `code.read_i32_const` and then calls the `on_i32_const`
hook. -/
theorem dispatch_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      Visitor.Core.run (code.read_i32_const st data) visitor.on_i32_const v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_DROP` runs `code.read_drop` and then calls the `on_drop` hook. -/
theorem dispatch_drop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      Visitor.Core.run (code.read_drop st) visitor.on_drop v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_UNREACHABLE` runs `code.read_unreachable` and then calls the
`on_unreachable` hook. -/
theorem dispatch_unreachable {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      Visitor.Core.run (code.read_unreachable st) (fun v s _ => visitor.on_unreachable v s) v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_I64_CONST` runs `code.read_i64_const` and then calls the `on_i64_const`
hook. -/
theorem dispatch_i64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      Visitor.Core.run (code.read_i64_const st data) visitor.on_i64_const v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_F32_CONST` runs `code.read_f32_const` and then calls the `on_f32_const`
hook. -/
theorem dispatch_f32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      Visitor.Core.run (code.read_f32_const st data) visitor.on_f32_const v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_F64_CONST` runs `code.read_f64_const` and then calls the `on_f64_const`
hook. -/
theorem dispatch_f64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      Visitor.Core.run (code.read_f64_const st data) visitor.on_f64_const v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_NOP` reads no immediates and calls the `on_nop` hook. -/
theorem dispatch_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v =
      Visitor.Core.run (.ok (.Ok (), st)) (fun v st (_ : Unit) => visitor.on_nop v st) v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- `code.step_memory` behaves as `code.step_numeric` on an opcode that is neither a load or store
nor `memory.size` or `memory.grow`. -/
theorem memory_fallback {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (opcode : U8) (v : V)
    (hm : Body.MemoryMeaning.opcodeMeaning opcode = none)
    (hsize : opcode ≠ code.OP_MEMORY_SIZE) (hgrow : opcode ≠ code.OP_MEMORY_GROW) :
    code.step_memory visitor st data env opcode v = code.step_numeric visitor st opcode v := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> first
    | with_unfolding_all rfl
    | exact False.elim (hsize (by with_unfolding_all rfl))
    | exact False.elim (hgrow (by with_unfolding_all rfl))
    | simp [Body.MemoryMeaning.opcodeMeaning, UScalar.val, BitVec.toNat] at hm

end Itasca.Visitor.Dispatch

end

/-! ## Erasure -/

section

/-!
# Erasing hooks from a run

`Visitor.Core.run.accepted` extracts the reader output and the accepting hook call from an accepted
`Visitor.Core.run`. `run.accepted_transfer` replays the run with another hook that accepts the same
outputs, which is how the later erasure theorems replace a visitor by `code.DefaultOpVisitor`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Erasure

export Computation (bind_ok_inv)

end Itasca.Visitor.Erasure

namespace Itasca.Visitor.Core

/-- An accepted run exposes the reader output and the accepting hook call that produced it. -/
theorem run.accepted {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (st' : code.OpIterState) (v' : V)
    (h : run read hook v = .ok (.Ok (), st', v')) :
    ∃ a, read = .ok (.Ok a, st') ∧ hook v st' a = .ok (.Ok (), v') := by
  unfold run at h
  obtain ⟨⟨res, st⟩, hr, hnext⟩ := Computation.bind_ok_inv _ _ _ h
  cases res with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  | Ok a =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
    obtain ⟨⟨vis, vout⟩, hv, hout⟩ := Computation.bind_ok_inv _ _ _ hnext
    cases vis with
    | Err e =>
      simp [code.visit,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
    | Ok u =>
      simp [code.visit] at hout
      obtain ⟨rfl, rfl⟩ := hout
      exact ⟨a, hr, hv⟩

/-- An accepted run carries over to any hook that accepts the same reader outputs at the same
state. -/
theorem run.accepted_transfer {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (replacement : W → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × W))
    (v : V) (w w' : W) (st' : code.OpIterState) (v' : V)
    (h : run read hook v = .ok (.Ok (), st', v'))
    (haccept : ∀ a, replacement w st' a = .ok (.Ok (), w')) :
    run read replacement w = .ok (.Ok (), st', w') := by
  obtain ⟨a, hr, _⟩ := run.accepted read hook v st' v' h
  simp [run, hr, haccept a, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Visitor.Core

end

/-! ## Events -/

section

/-!
# Visitor events

The public `Event` and `Observation` definitions describe a callback and its result.
`invoke` calls the named hook; `ofHandler` builds a visitor from a single event handler.
`invoke_of_handler` proves their agreement for the complete operator callback interface.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- Builds a visitor whose every hook forwards its event to one handler. -/
def ofHandler {V : Type} (handler : V → Event → Result (VisitResult × V)) :
    code.OpVisitor V where
  on_function_start v ctx typeidx bodybegin bodyend :=
    handler v (.functionStart ctx typeidx bodybegin bodyend)
  on_unreachable v st := handler v (.op st (.unreachable))
  on_nop v st := handler v (.op st (.nop))
  on_block v st a0 := handler v (.op st (.block a0))
  on_loop v st a0 := handler v (.op st (.loop a0))
  on_if v st a0 := handler v (.op st (.if_ a0))
  on_else v st a0 := handler v (.op st (.else_ a0))
  on_end v st a0 a1 := handler v (.op st (.end_ a0 a1))
  on_br v st a0 a1 := handler v (.op st (.br a0 a1))
  on_br_if v st a0 a1 := handler v (.op st (.br_if a0 a1))
  on_br_table_label v st a0 := handler v (.op st (.br_table_label a0))
  on_br_table v st a0 a1 := handler v (.op st (.br_table a0 a1))
  on_return v st := handler v (.op st (.return_))
  on_call v st a0 := handler v (.op st (.call a0))
  on_call_indirect v st a0 a1 := handler v (.op st (.call_indirect a0 a1))
  on_drop v st a0 := handler v (.op st (.drop a0))
  on_select v st a0 := handler v (.op st (.select a0))
  on_local_get v st a0 := handler v (.op st (.local_get a0))
  on_local_set v st a0 := handler v (.op st (.local_set a0))
  on_local_tee v st a0 := handler v (.op st (.local_tee a0))
  on_global_get v st a0 := handler v (.op st (.global_get a0))
  on_global_set v st a0 := handler v (.op st (.global_set a0))
  on_memory_size v st := handler v (.op st (.memory_size))
  on_memory_grow v st := handler v (.op st (.memory_grow))
  on_i32_const v st a0 := handler v (.op st (.i32_const a0))
  on_i64_const v st a0 := handler v (.op st (.i64_const a0))
  on_f32_const v st a0 := handler v (.op st (.f32_const a0))
  on_f64_const v st a0 := handler v (.op st (.f64_const a0))
  on_i32_load v st arg := handler v (.op st (.memory .i32_load arg))
  on_i64_load v st arg := handler v (.op st (.memory .i64_load arg))
  on_f32_load v st arg := handler v (.op st (.memory .f32_load arg))
  on_f64_load v st arg := handler v (.op st (.memory .f64_load arg))
  on_i32_load8_s v st arg := handler v (.op st (.memory .i32_load8_s arg))
  on_i32_load8_u v st arg := handler v (.op st (.memory .i32_load8_u arg))
  on_i32_load16_s v st arg := handler v (.op st (.memory .i32_load16_s arg))
  on_i32_load16_u v st arg := handler v (.op st (.memory .i32_load16_u arg))
  on_i64_load8_s v st arg := handler v (.op st (.memory .i64_load8_s arg))
  on_i64_load8_u v st arg := handler v (.op st (.memory .i64_load8_u arg))
  on_i64_load16_s v st arg := handler v (.op st (.memory .i64_load16_s arg))
  on_i64_load16_u v st arg := handler v (.op st (.memory .i64_load16_u arg))
  on_i64_load32_s v st arg := handler v (.op st (.memory .i64_load32_s arg))
  on_i64_load32_u v st arg := handler v (.op st (.memory .i64_load32_u arg))
  on_i32_store v st arg := handler v (.op st (.memory .i32_store arg))
  on_i64_store v st arg := handler v (.op st (.memory .i64_store arg))
  on_f32_store v st arg := handler v (.op st (.memory .f32_store arg))
  on_f64_store v st arg := handler v (.op st (.memory .f64_store arg))
  on_i32_store8 v st arg := handler v (.op st (.memory .i32_store8 arg))
  on_i32_store16 v st arg := handler v (.op st (.memory .i32_store16 arg))
  on_i64_store8 v st arg := handler v (.op st (.memory .i64_store8 arg))
  on_i64_store16 v st arg := handler v (.op st (.memory .i64_store16 arg))
  on_i64_store32 v st arg := handler v (.op st (.memory .i64_store32 arg))
  on_i32_eqz v st := handler v (.op st (.numeric .i32_eqz))
  on_i32_eq v st := handler v (.op st (.numeric .i32_eq))
  on_i32_ne v st := handler v (.op st (.numeric .i32_ne))
  on_i32_lt_s v st := handler v (.op st (.numeric .i32_lt_s))
  on_i32_lt_u v st := handler v (.op st (.numeric .i32_lt_u))
  on_i32_gt_s v st := handler v (.op st (.numeric .i32_gt_s))
  on_i32_gt_u v st := handler v (.op st (.numeric .i32_gt_u))
  on_i32_le_s v st := handler v (.op st (.numeric .i32_le_s))
  on_i32_le_u v st := handler v (.op st (.numeric .i32_le_u))
  on_i32_ge_s v st := handler v (.op st (.numeric .i32_ge_s))
  on_i32_ge_u v st := handler v (.op st (.numeric .i32_ge_u))
  on_i64_eqz v st := handler v (.op st (.numeric .i64_eqz))
  on_i64_eq v st := handler v (.op st (.numeric .i64_eq))
  on_i64_ne v st := handler v (.op st (.numeric .i64_ne))
  on_i64_lt_s v st := handler v (.op st (.numeric .i64_lt_s))
  on_i64_lt_u v st := handler v (.op st (.numeric .i64_lt_u))
  on_i64_gt_s v st := handler v (.op st (.numeric .i64_gt_s))
  on_i64_gt_u v st := handler v (.op st (.numeric .i64_gt_u))
  on_i64_le_s v st := handler v (.op st (.numeric .i64_le_s))
  on_i64_le_u v st := handler v (.op st (.numeric .i64_le_u))
  on_i64_ge_s v st := handler v (.op st (.numeric .i64_ge_s))
  on_i64_ge_u v st := handler v (.op st (.numeric .i64_ge_u))
  on_f32_eq v st := handler v (.op st (.numeric .f32_eq))
  on_f32_ne v st := handler v (.op st (.numeric .f32_ne))
  on_f32_lt v st := handler v (.op st (.numeric .f32_lt))
  on_f32_gt v st := handler v (.op st (.numeric .f32_gt))
  on_f32_le v st := handler v (.op st (.numeric .f32_le))
  on_f32_ge v st := handler v (.op st (.numeric .f32_ge))
  on_f64_eq v st := handler v (.op st (.numeric .f64_eq))
  on_f64_ne v st := handler v (.op st (.numeric .f64_ne))
  on_f64_lt v st := handler v (.op st (.numeric .f64_lt))
  on_f64_gt v st := handler v (.op st (.numeric .f64_gt))
  on_f64_le v st := handler v (.op st (.numeric .f64_le))
  on_f64_ge v st := handler v (.op st (.numeric .f64_ge))
  on_i32_sub v st := handler v (.op st (.numeric .i32_sub))
  on_i32_mul v st := handler v (.op st (.numeric .i32_mul))
  on_i32_div_s v st := handler v (.op st (.numeric .i32_div_s))
  on_i32_div_u v st := handler v (.op st (.numeric .i32_div_u))
  on_i32_rem_s v st := handler v (.op st (.numeric .i32_rem_s))
  on_i32_rem_u v st := handler v (.op st (.numeric .i32_rem_u))
  on_i32_and v st := handler v (.op st (.numeric .i32_and))
  on_i32_or v st := handler v (.op st (.numeric .i32_or))
  on_i32_xor v st := handler v (.op st (.numeric .i32_xor))
  on_i32_shl v st := handler v (.op st (.numeric .i32_shl))
  on_i32_shr_s v st := handler v (.op st (.numeric .i32_shr_s))
  on_i32_shr_u v st := handler v (.op st (.numeric .i32_shr_u))
  on_i32_rotl v st := handler v (.op st (.numeric .i32_rotl))
  on_i32_rotr v st := handler v (.op st (.numeric .i32_rotr))
  on_i64_add v st := handler v (.op st (.numeric .i64_add))
  on_i64_sub v st := handler v (.op st (.numeric .i64_sub))
  on_i64_mul v st := handler v (.op st (.numeric .i64_mul))
  on_i64_div_s v st := handler v (.op st (.numeric .i64_div_s))
  on_i64_div_u v st := handler v (.op st (.numeric .i64_div_u))
  on_i64_rem_s v st := handler v (.op st (.numeric .i64_rem_s))
  on_i64_rem_u v st := handler v (.op st (.numeric .i64_rem_u))
  on_i64_and v st := handler v (.op st (.numeric .i64_and))
  on_i64_or v st := handler v (.op st (.numeric .i64_or))
  on_i64_xor v st := handler v (.op st (.numeric .i64_xor))
  on_i64_shl v st := handler v (.op st (.numeric .i64_shl))
  on_i64_shr_s v st := handler v (.op st (.numeric .i64_shr_s))
  on_i64_shr_u v st := handler v (.op st (.numeric .i64_shr_u))
  on_i64_rotl v st := handler v (.op st (.numeric .i64_rotl))
  on_i64_rotr v st := handler v (.op st (.numeric .i64_rotr))
  on_f32_add v st := handler v (.op st (.numeric .f32_add))
  on_f32_sub v st := handler v (.op st (.numeric .f32_sub))
  on_f32_mul v st := handler v (.op st (.numeric .f32_mul))
  on_f32_div v st := handler v (.op st (.numeric .f32_div))
  on_f32_min v st := handler v (.op st (.numeric .f32_min))
  on_f32_max v st := handler v (.op st (.numeric .f32_max))
  on_f32_copysign v st := handler v (.op st (.numeric .f32_copysign))
  on_f64_add v st := handler v (.op st (.numeric .f64_add))
  on_f64_sub v st := handler v (.op st (.numeric .f64_sub))
  on_f64_mul v st := handler v (.op st (.numeric .f64_mul))
  on_f64_div v st := handler v (.op st (.numeric .f64_div))
  on_f64_min v st := handler v (.op st (.numeric .f64_min))
  on_f64_max v st := handler v (.op st (.numeric .f64_max))
  on_f64_copysign v st := handler v (.op st (.numeric .f64_copysign))
  on_i32_clz v st := handler v (.op st (.numeric .i32_clz))
  on_i32_ctz v st := handler v (.op st (.numeric .i32_ctz))
  on_i32_popcnt v st := handler v (.op st (.numeric .i32_popcnt))
  on_i32_add v st := handler v (.op st (.numeric .i32_add))
  on_i64_clz v st := handler v (.op st (.numeric .i64_clz))
  on_i64_ctz v st := handler v (.op st (.numeric .i64_ctz))
  on_i64_popcnt v st := handler v (.op st (.numeric .i64_popcnt))
  on_f32_abs v st := handler v (.op st (.numeric .f32_abs))
  on_f32_neg v st := handler v (.op st (.numeric .f32_neg))
  on_f32_ceil v st := handler v (.op st (.numeric .f32_ceil))
  on_f32_floor v st := handler v (.op st (.numeric .f32_floor))
  on_f32_trunc v st := handler v (.op st (.numeric .f32_trunc))
  on_f32_nearest v st := handler v (.op st (.numeric .f32_nearest))
  on_f32_sqrt v st := handler v (.op st (.numeric .f32_sqrt))
  on_f64_abs v st := handler v (.op st (.numeric .f64_abs))
  on_f64_neg v st := handler v (.op st (.numeric .f64_neg))
  on_f64_ceil v st := handler v (.op st (.numeric .f64_ceil))
  on_f64_floor v st := handler v (.op st (.numeric .f64_floor))
  on_f64_trunc v st := handler v (.op st (.numeric .f64_trunc))
  on_f64_nearest v st := handler v (.op st (.numeric .f64_nearest))
  on_f64_sqrt v st := handler v (.op st (.numeric .f64_sqrt))
  on_i32_wrap_i64 v st := handler v (.op st (.numeric .i32_wrap_i64))
  on_i32_trunc_f32_s v st := handler v (.op st (.numeric .i32_trunc_f32_s))
  on_i32_trunc_f32_u v st := handler v (.op st (.numeric .i32_trunc_f32_u))
  on_i32_trunc_f64_s v st := handler v (.op st (.numeric .i32_trunc_f64_s))
  on_i32_trunc_f64_u v st := handler v (.op st (.numeric .i32_trunc_f64_u))
  on_i64_extend_i32_s v st := handler v (.op st (.numeric .i64_extend_i32_s))
  on_i64_extend_i32_u v st := handler v (.op st (.numeric .i64_extend_i32_u))
  on_i64_trunc_f32_s v st := handler v (.op st (.numeric .i64_trunc_f32_s))
  on_i64_trunc_f32_u v st := handler v (.op st (.numeric .i64_trunc_f32_u))
  on_i64_trunc_f64_s v st := handler v (.op st (.numeric .i64_trunc_f64_s))
  on_i64_trunc_f64_u v st := handler v (.op st (.numeric .i64_trunc_f64_u))
  on_f32_convert_i32_s v st := handler v (.op st (.numeric .f32_convert_i32_s))
  on_f32_convert_i32_u v st := handler v (.op st (.numeric .f32_convert_i32_u))
  on_f32_convert_i64_s v st := handler v (.op st (.numeric .f32_convert_i64_s))
  on_f32_convert_i64_u v st := handler v (.op st (.numeric .f32_convert_i64_u))
  on_f32_demote_f64 v st := handler v (.op st (.numeric .f32_demote_f64))
  on_f64_convert_i32_s v st := handler v (.op st (.numeric .f64_convert_i32_s))
  on_f64_convert_i32_u v st := handler v (.op st (.numeric .f64_convert_i32_u))
  on_f64_convert_i64_s v st := handler v (.op st (.numeric .f64_convert_i64_s))
  on_f64_convert_i64_u v st := handler v (.op st (.numeric .f64_convert_i64_u))
  on_f64_promote_f32 v st := handler v (.op st (.numeric .f64_promote_f32))
  on_i32_reinterpret_f32 v st := handler v (.op st (.numeric .i32_reinterpret_f32))
  on_i64_reinterpret_f64 v st := handler v (.op st (.numeric .i64_reinterpret_f64))
  on_f32_reinterpret_i32 v st := handler v (.op st (.numeric .f32_reinterpret_i32))
  on_f64_reinterpret_i64 v st := handler v (.op st (.numeric .f64_reinterpret_i64))
  on_i32_extend8_s v st := handler v (.op st (.extendedNumeric .i32_extend8_s))
  on_i32_extend16_s v st := handler v (.op st (.extendedNumeric .i32_extend16_s))
  on_i64_extend8_s v st := handler v (.op st (.extendedNumeric .i64_extend8_s))
  on_i64_extend16_s v st := handler v (.op st (.extendedNumeric .i64_extend16_s))
  on_i64_extend32_s v st := handler v (.op st (.extendedNumeric .i64_extend32_s))
  on_i32_trunc_sat_f32_s v st := handler v (.op st (.extendedNumeric .i32_trunc_sat_f32_s))
  on_i32_trunc_sat_f32_u v st := handler v (.op st (.extendedNumeric .i32_trunc_sat_f32_u))
  on_i32_trunc_sat_f64_s v st := handler v (.op st (.extendedNumeric .i32_trunc_sat_f64_s))
  on_i32_trunc_sat_f64_u v st := handler v (.op st (.extendedNumeric .i32_trunc_sat_f64_u))
  on_i64_trunc_sat_f32_s v st := handler v (.op st (.extendedNumeric .i64_trunc_sat_f32_s))
  on_i64_trunc_sat_f32_u v st := handler v (.op st (.extendedNumeric .i64_trunc_sat_f32_u))
  on_i64_trunc_sat_f64_s v st := handler v (.op st (.extendedNumeric .i64_trunc_sat_f64_s))
  on_i64_trunc_sat_f64_u v st := handler v (.op st (.extendedNumeric .i64_trunc_sat_f64_u))

  on_ref_null v st a0 := handler v (.op st (.ref_null a0))
  on_ref_is_null v st := handler v (.op st (.ref_is_null))
  on_ref_func v st a0 := handler v (.op st (.ref_func a0))
  on_select_typed v st a0 := handler v (.op st (.select_typed a0))
  on_table_get v st a0 := handler v (.op st (.table_get a0))
  on_table_set v st a0 := handler v (.op st (.table_set a0))
  on_memory_init v st a0 := handler v (.op st (.memory_init a0))
  on_data_drop v st a0 := handler v (.op st (.data_drop a0))
  on_memory_copy v st := handler v (.op st (.memory_copy))
  on_memory_fill v st := handler v (.op st (.memory_fill))
  on_table_init v st a0 a1 := handler v (.op st (.table_init a0 a1))
  on_elem_drop v st a0 := handler v (.op st (.elem_drop a0))
  on_table_copy v st a0 a1 := handler v (.op st (.table_copy a0 a1))
  on_table_grow v st a0 := handler v (.op st (.table_grow a0))
  on_table_size v st a0 := handler v (.op st (.table_size a0))
  on_table_fill v st a0 := handler v (.op st (.table_fill a0))
  on_simd v st a0 := handler v (.op st (.simd a0))
  on_simd_lane v st a0 a1 := handler v (.op st (.simd_lane a0 a1))
  on_simd_memory v st a0 a1 := handler v (.op st (.simd_memory a0 a1))
  on_simd_memory_lane v st a0 a1 a2 := handler v (.op st (.simd_memory_lane a0 a1 a2))
  on_simd_const v st a0 a1 := handler v (.op st (.simd_const a0 a1))
  on_simd_shuffle v st a0 a1 := handler v (.op st (.simd_shuffle a0 a1))


/-- Invoking a visitor built by `ofHandler` runs the handler on the event. -/
@[simp] theorem invoke_of_handler {V : Type}
    (handler : V → Event → Result (VisitResult × V)) (v : V) (event : Event) :
    invoke (ofHandler handler) v event = handler v event := by
  cases event with
  | functionStart ctx typeidx bodybegin bodyend => rfl
  | op st action =>
    cases action <;> try rfl
    all_goals first | (cases ‹NumericHook› <;> rfl) | (cases ‹ExtendedNumericHook› <;> rfl) | (cases ‹MemoryHook› <;> rfl)

end Itasca.Visitor.Trace

end

end

/-! ## RunTrace -/

section

/-!
# Run Trace

Callback step erasure and lifting agree with the transparent recorder. Recorded runs preserve the actual event order and returned visitor state.
-/

/-! ## StepErasure -/

section

/-!
# Erasing the visitor from an accepted step

`code.step.accepted_erase` shows that if `code.step` accepts an instruction with any visitor, it
accepts it with `code.DefaultOpVisitor` and reaches the same validator state. The proof dispatches
on the opcode using `Visitor/Events`; the branch-table erasure lemmas below handle its nested
label hooks. The result covers the extracted scalar step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Erasure

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The empty visitor accepts every numeric opcode. -/
theorem visit_numeric_empty (st : code.OpIterState) (opcode : U8) :
    code.visit_numeric code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor () st opcode =
      .ok (.Ok (), ()) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The empty visitor accepts every load and store opcode. -/
theorem visit_memory_empty (st : code.OpIterState) (opcode : U8) (arg : code.MemArg) :
    code.visit_memory code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor () st opcode arg =
      .ok (.Ok (), ()) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

end Itasca.Visitor.Erasure

namespace Itasca

/-- An accepted `code.step_numeric` run also succeeds, at the same state, with the empty visitor. -/
theorem code.step_numeric.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (opcode : U8) (v v' : V)
    (h : code.step_numeric visitor st opcode v = .ok (.Ok (), st', v')) :
    code.step_numeric code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor st opcode () =
      .ok (.Ok (), st', ()) := by
  cases hm : Body.Numeric.opcodeMeaning opcode with
  | none => simp [code.step_numeric.unrecognized visitor st opcode v hm] at h
  | some op =>
    rw [code.step_numeric.dispatch visitor st opcode op v hm] at h
    rw [code.step_numeric.dispatch _ st opcode op () hm]
    exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h
      (fun _ => Visitor.Erasure.visit_numeric_empty st' opcode)

set_option maxHeartbeats 1000000 in
/-- An accepted `code.step` run also succeeds, at the same state, with the empty visitor. -/
theorem code.step.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context)
    (opcode : U8) (v v' : V)
    (h : code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v')) :
    code.step code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), st', ()) := by
  cases hm : Body.MemoryMeaning.opcodeMeaning opcode with
  | some op =>
    rw [code.step_memory.dispatch visitor st data env ctx v opcode op hm] at h
    rw [code.step_memory.dispatch _ st data env ctx () opcode op hm]
    exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h
      (fun _ => Visitor.Erasure.visit_memory_empty st' opcode _)
  | none =>
    by_cases h_nop : opcode = code.OP_NOP
    · subst opcode
      rw [Visitor.Dispatch.dispatch_nop visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_nop _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_unreachable : opcode = code.OP_UNREACHABLE
    · subst opcode
      rw [Visitor.Dispatch.dispatch_unreachable visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_unreachable _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_i32_const : opcode = code.OP_I32_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_i32_const visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_i32_const _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_i64_const : opcode = code.OP_I64_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_i64_const visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_i64_const _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_f32_const : opcode = code.OP_F32_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_f32_const visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_f32_const _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_f64_const : opcode = code.OP_F64_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_f64_const visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_f64_const _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_drop : opcode = code.OP_DROP
    · subst opcode
      rw [Visitor.Dispatch.dispatch_drop visitor st data env ctx v] at h
      rw [Visitor.Dispatch.dispatch_drop _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_select : opcode = code.OP_SELECT
    · subst opcode
      rw [code.step_select.dispatch visitor st data env ctx v] at h
      rw [code.step_select.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_local_get : opcode = code.OP_LOCAL_GET
    · subst opcode
      rw [code.step_local_get.dispatch visitor st data env ctx v] at h
      rw [code.step_local_get.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_local_set : opcode = code.OP_LOCAL_SET
    · subst opcode
      rw [code.step_local_set.dispatch visitor st data env ctx v] at h
      rw [code.step_local_set.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
    · subst opcode
      rw [code.step_local_tee.dispatch visitor st data env ctx v] at h
      rw [code.step_local_tee.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_global_get : opcode = code.OP_GLOBAL_GET
    · subst opcode
      rw [code.step_global_get.dispatch visitor st data env ctx v] at h
      rw [code.step_global_get.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_global_set : opcode = code.OP_GLOBAL_SET
    · subst opcode
      rw [code.step_global_set.dispatch visitor st data env ctx v] at h
      rw [code.step_global_set.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
    · subst opcode
      rw [code.step_memory_size.dispatch visitor st data env ctx v] at h
      rw [code.step_memory_size.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
    · subst opcode
      rw [code.step_memory_grow.dispatch visitor st data env ctx v] at h
      rw [code.step_memory_grow.dispatch _ st data env ctx ()]
      exact Visitor.Core.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    have heqval (a b : U8) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
        code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
      unfold code.step
      split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
    rw [hdispatch visitor v] at h
    rw [hdispatch _ ()]
    rw [Visitor.Dispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow] at h
    rw [Visitor.Dispatch.memory_fallback _ st data env opcode () hm h_memory_size h_memory_grow]
    exact code.step_numeric.accepted_erase visitor st st' opcode v v' h

end Itasca

end

/-! ## StepLift -/

section

/-!
# Lifting an accepted step to an accepting visitor

The converse of `code.step.accepted_erase`. `code.step.accepted_lift` shows that if `code.step` accepts
with `code.DefaultOpVisitor`, it also accepts, at the same validator state, with any visitor
satisfying `Visitor.Accepts`. The `br_table` label loop is lifted in
`code.read_table_labels_loop.accepted_lift`. Covers the scalar step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Core

/-- An accepted `Visitor.Core.run` can be replayed with any hook that accepts the reader output. -/
theorem run.accepted_lift {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (replacement : W → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × W))
    (v : V) (w : W) (st' : code.OpIterState) (v' : V)
    (h : run read hook v = .ok (.Ok (), st', v'))
    (haccept : ∀ a, ∃ w', replacement w st' a = .ok (.Ok (), w')) :
    ∃ w', run read replacement w = .ok (.Ok (), st', w') := by
  obtain ⟨a, hr, _⟩ := run.accepted read hook v st' v' h
  obtain ⟨w', hw⟩ := haccept a
  exact ⟨w', by simp [run, hr, hw, code.visit, core.result.Result.Insts.CoreOpsTry.branch]⟩

end Itasca.Visitor.Core

namespace Itasca

/-- `code.step_numeric` accepts with any accepting visitor whenever it does with the empty visitor,
at the same state. -/
theorem code.step_numeric.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : Visitor.Accepts visitor)
    (st st' : code.OpIterState) (opcode : U8) (v : V)
    (h : code.step_numeric code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor st opcode () =
      .ok (.Ok (), st', ())) :
    ∃ v', code.step_numeric visitor st opcode v = .ok (.Ok (), st', v') := by
  cases hm : Body.Numeric.opcodeMeaning opcode with
  | none => simp [code.step_numeric.unrecognized _ st opcode () hm] at h
  | some op =>
    rw [code.step_numeric.dispatch _ st opcode op () hm] at h
    rw [code.step_numeric.dispatch visitor st opcode op v hm]
    exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
      (fun _ => haccept.visit_numeric v st' opcode)

set_option maxHeartbeats 1000000 in
/-- If `code.step` accepts with the empty visitor, it accepts at the same state with any visitor
whose hooks all accept. The resulting visitor state is unconstrained. -/
theorem code.step.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : Visitor.Accepts visitor)
    (st st' : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context)
    (opcode : U8) (v : V)
    (h : code.step code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), st', ())) :
    ∃ v', code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v') := by
  cases hm : Body.MemoryMeaning.opcodeMeaning opcode with
  | some op =>
    rw [code.step_memory.dispatch _ st data env ctx () opcode op hm] at h
    rw [code.step_memory.dispatch visitor st data env ctx v opcode op hm]
    exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
      (fun arg => haccept.visit_memory v st' opcode arg)
  | none =>
    by_cases h_nop : opcode = code.OP_NOP
    · subst opcode
      rw [Visitor.Dispatch.dispatch_nop _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_nop visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_nop v st')
    by_cases h_unreachable : opcode = code.OP_UNREACHABLE
    · subst opcode
      rw [Visitor.Dispatch.dispatch_unreachable _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_unreachable visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_unreachable v st')
    by_cases h_i32_const : opcode = code.OP_I32_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_i32_const _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_i32_const visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_i32_const v st' a)
    by_cases h_i64_const : opcode = code.OP_I64_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_i64_const _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_i64_const visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_i64_const v st' a)
    by_cases h_f32_const : opcode = code.OP_F32_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_f32_const _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_f32_const visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_f32_const v st' a)
    by_cases h_f64_const : opcode = code.OP_F64_CONST
    · subst opcode
      rw [Visitor.Dispatch.dispatch_f64_const _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_f64_const visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_f64_const v st' a)
    by_cases h_drop : opcode = code.OP_DROP
    · subst opcode
      rw [Visitor.Dispatch.dispatch_drop _ st data env ctx ()] at h
      rw [Visitor.Dispatch.dispatch_drop visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_drop v st' a)
    by_cases h_select : opcode = code.OP_SELECT
    · subst opcode
      rw [code.step_select.dispatch _ st data env ctx ()] at h
      rw [code.step_select.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_select v st' a)
    by_cases h_local_get : opcode = code.OP_LOCAL_GET
    · subst opcode
      rw [code.step_local_get.dispatch _ st data env ctx ()] at h
      rw [code.step_local_get.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_local_get v st' a)
    by_cases h_local_set : opcode = code.OP_LOCAL_SET
    · subst opcode
      rw [code.step_local_set.dispatch _ st data env ctx ()] at h
      rw [code.step_local_set.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_local_set v st' a)
    by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
    · subst opcode
      rw [code.step_local_tee.dispatch _ st data env ctx ()] at h
      rw [code.step_local_tee.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_local_tee v st' a)
    by_cases h_global_get : opcode = code.OP_GLOBAL_GET
    · subst opcode
      rw [code.step_global_get.dispatch _ st data env ctx ()] at h
      rw [code.step_global_get.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_global_get v st' a)
    by_cases h_global_set : opcode = code.OP_GLOBAL_SET
    · subst opcode
      rw [code.step_global_set.dispatch _ st data env ctx ()] at h
      rw [code.step_global_set.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_global_set v st' a)
    by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
    · subst opcode
      rw [code.step_memory_size.dispatch _ st data env ctx ()] at h
      rw [code.step_memory_size.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_memory_size v st')
    by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
    · subst opcode
      rw [code.step_memory_grow.dispatch _ st data env ctx ()] at h
      rw [code.step_memory_grow.dispatch visitor st data env ctx v]
      exact Visitor.Core.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_memory_grow v st')
    have heqval (a b : U8) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
        code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
      unfold code.step
      split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
    rw [hdispatch _ ()] at h
    rw [hdispatch visitor v]
    rw [Visitor.Dispatch.memory_fallback _ st data env opcode () hm h_memory_size h_memory_grow] at h
    rw [Visitor.Dispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow]
    exact code.step_numeric.accepted_lift visitor haccept st st' opcode v h

end Itasca

end

/-! ## Recording -/

section

/-!
# Recording visitors

`Visitor.Trace.Records` specifies the log extension of every returning callback.
`instrument_records` proves the logging wrapper satisfies it. `recorder` accepts
every hook. The invoke/acceptance lemmas and recorder contracts connect these
operations to the full visitor interface.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- Appends a callback's event and reply to a log, keeping the wrapped visitor's reply and state. -/
def record {V : Type} (log : List Observation) (event : Event)
    (action : Result (VisitResult × V)) : Result (VisitResult × (V × List Observation)) := do
  let (reply, v') ← action
  .ok (reply, (v', log ++ [⟨event, reply⟩]))

/-- Wraps a visitor so that it also logs every callback with its reply. The wrapped visitor still
decides every reply. -/
def instrument {V : Type} (visitor : code.OpVisitor V) :
    code.OpVisitor (V × List Observation) :=
  ofHandler fun state event => record state.2 event (invoke visitor state.1 event)

/-- A visitor whose state is the log of its callbacks and which accepts every callback. -/
def recorder : code.OpVisitor (List Observation) :=
  ofHandler fun log event => .ok (.Ok (), log ++ [⟨event, .Ok ()⟩])


@[simp] theorem record_ok {V : Type} (log : List Observation) (event : Event)
    (reply : VisitResult) (v' : V) :
    record log event (.ok (reply, v')) = .ok (reply, (v', log ++ [⟨event, reply⟩])) := by
  simp [record]

theorem record_ok_iff {V : Type} (log : List Observation) (event : Event)
    (action : Result (VisitResult × V)) (reply : VisitResult) (v' : V)
    (log' : List Observation) :
    record log event action = .ok (reply, (v', log')) ↔
      action = .ok (reply, v') ∧ log' = log ++ [⟨event, reply⟩] := by
  constructor
  · intro h
    unfold record at h
    obtain ⟨⟨r, w⟩, ha, hb⟩ := Computation.bind_ok_inv _ _ _ h
    simp at hb
    rcases hb with ⟨rfl, rfl, rfl⟩
    exact ⟨ha, rfl⟩
  · rintro ⟨h, rfl⟩
    simp [h]

@[simp] theorem invoke_instrument {V : Type} (visitor : code.OpVisitor V)
    (v : V) (log : List Observation) (event : Event) :
    invoke (instrument visitor) (v, log) event = record log event (invoke visitor v event) := by
  simp [instrument]

/-- The log of an instrumented visitor records every callback. -/
theorem instrument_records {V : Type} (visitor : code.OpVisitor V) :
    Records (instrument visitor) Prod.snd := by
  rintro ⟨v, log⟩ event reply ⟨v', log'⟩ h
  exact ((record_ok_iff log event _ reply v' log').mp (by simpa using h)).2

/-- Event-wise acceptance is exactly the public accepting-visitor contract. -/
theorem accepts_of_invoke {V : Type} (visitor : code.OpVisitor V)
    (h : ∀ v event, ∃ v', invoke visitor v event = .ok (.Ok (), v')) : Visitor.Accepts visitor := h

/-- `recorder` records every callback. -/
theorem recorder_records : Records recorder id := by
  intro log event reply log' h
  simp [recorder] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- `recorder` accepts. -/
theorem recorder_accepts : Visitor.Accepts recorder := by
  apply accepts_of_invoke
  intro log event
  exact ⟨log ++ [⟨event, .Ok ()⟩], by simp [recorder]⟩

/-- `recorder` is total. -/
theorem recorder_total : Visitor.Total recorder :=
  recorder_accepts.to_total

end Itasca.Visitor.Trace

end

/-! ## RunTrace -/

section

/-!
# One instruction step with a recording visitor

`Visitor.Core.run.returned_iff` characterizes an ordinary return: the reader
failed before any hook, or the hook ran once. `run.recorded` identifies the
observations appended by a recording visitor. Callback correspondence is
expressed separately by `Visitor.Trace.Refines`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- The validator error for a callback reply: a rejection becomes `OpError.Visitor`. -/
def hookResult : VisitResult → core.result.Result Unit error.OpError
  | .Ok _ => .Ok ()
  | .Err e => .Err (.Visitor e)

end Itasca.Visitor.Trace

namespace Itasca.Visitor.Core

open Visitor.Trace

/-- A run that returns normally either failed in its reader and made no hook call, or called its
hook once at the state the reader produced. -/
theorem run.returned_iff {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (VisitResult × V))
    (v : V) (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V) :
    run read hook v = .ok (res, st', v') ↔
      (∃ err, read = .ok (.Err err, st') ∧ res = .Err err ∧ v' = v) ∨
      (∃ a reply, read = .ok (.Ok a, st') ∧ hook v st' a = .ok (reply, v') ∧
        res = hookResult reply) := by
  constructor
  · intro h
    unfold run at h
    obtain ⟨⟨r, st⟩, hr, hnext⟩ := Computation.bind_ok_inv _ _ _ h
    cases r with
    | Err err =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
      rcases hnext with ⟨rfl, rfl, rfl⟩
      exact Or.inl ⟨err, hr, rfl, rfl⟩
    | Ok a =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
      obtain ⟨⟨reply, w⟩, hv, hout⟩ := Computation.bind_ok_inv _ _ _ hnext
      cases reply with
      | Err err =>
        simp [code.visit,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
        rcases hout with ⟨rfl, rfl, rfl⟩
        exact Or.inr ⟨a, .Err err, hr, hv, rfl⟩
      | Ok u =>
        simp [code.visit] at hout
        rcases hout with ⟨rfl, rfl, rfl⟩
        exact Or.inr ⟨a, .Ok u, hr, hv, rfl⟩
  · rintro (⟨err, hr, rfl, rfl⟩ | ⟨a, reply, hr, hv, rfl⟩)
    · simp [run, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · cases reply <;> simp [run, hr, hv, hookResult, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- With a recording visitor, a run that returns normally records nothing when the reader fails and
exactly one observation, the event and its reply, when the reader succeeds. -/
theorem run.recorded {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (event : code.OpIterState → A → Event)
    (v : V) (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : run read (fun v st a => invoke visitor v (event st a)) v = .ok (res, st', v')) :
    (∃ err, read = .ok (.Err err, st') ∧ res = .Err err ∧ observe v' = observe v) ∨
    (∃ a reply, read = .ok (.Ok a, st') ∧ res = hookResult reply ∧
      observe v' = observe v ++ [⟨event st' a, reply⟩]) := by
  rcases (run.returned_iff _ _ _ _ _ _).mp h with
    ⟨err, hr, he, rfl⟩ | ⟨a, reply, hr, hv, he⟩
  · exact Or.inl ⟨err, hr, he, rfl⟩
  · exact Or.inr ⟨a, reply, hr, he, hrecords v (event st' a) reply v' hv⟩

end Itasca.Visitor.Core

end

end
