import Itasca.Visitor.Basic
import Itasca.Binary.Wasm1.MemoryMeaning
import Mathlib.Tactic.IntervalCases

/-!
# Step dispatch for control and constant instructions

For each control and constant opcode, `OpDispatch.dispatch_*` rewrites `code.step` at that opcode
to `CoreVisitor.run` of the instruction's reader and its visitor hook. `memory_fallback` shows
`code.step_memory` falls through to `code.step_numeric` for opcodes outside the memory table.
Covers the Wasm 1.0 step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.OpDispatch

/-- `code.step` on `code.OP_I32_CONST` runs `code.read_i32_const` and then calls the `on_i32_const`
hook. -/
theorem dispatch_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      CoreVisitor.run (code.read_i32_const st data) visitor.on_i32_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_DROP` runs `code.read_drop` and then calls the `on_drop` hook. -/
theorem dispatch_drop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      CoreVisitor.run (code.read_drop st) visitor.on_drop v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_UNREACHABLE` runs `code.read_unreachable` and then calls the
`on_unreachable` hook. -/
theorem dispatch_unreachable {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      CoreVisitor.run (code.read_unreachable st) (fun v s _ => visitor.on_unreachable v s) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_I64_CONST` runs `code.read_i64_const` and then calls the `on_i64_const`
hook. -/
theorem dispatch_i64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) visitor.on_i64_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_F32_CONST` runs `code.read_f32_const` and then calls the `on_f32_const`
hook. -/
theorem dispatch_f32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) visitor.on_f32_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_F64_CONST` runs `code.read_f64_const` and then calls the `on_f64_const`
hook. -/
theorem dispatch_f64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) visitor.on_f64_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- `code.step` on `code.OP_NOP` reads no immediates and calls the `on_nop` hook. -/
theorem dispatch_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v =
      CoreVisitor.run (.ok (.Ok (), st)) (fun v st (_ : Unit) => visitor.on_nop v st) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- `code.step_memory` behaves as `code.step_numeric` on an opcode that is neither a load or store
nor `memory.size` or `memory.grow`. -/
theorem memory_fallback {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U8) (v : V)
    (hm : MemoryMeaning.opcodeMeaning opcode = none)
    (hsize : opcode ≠ code.OP_MEMORY_SIZE) (hgrow : opcode ≠ code.OP_MEMORY_GROW) :
    code.step_memory visitor st data env opcode v = code.step_numeric visitor st opcode v := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> first
    | with_unfolding_all rfl
    | exact False.elim (hsize (by with_unfolding_all rfl))
    | exact False.elim (hgrow (by with_unfolding_all rfl))
    | simp [MemoryMeaning.opcodeMeaning, UScalar.val, BitVec.toNat] at hm

end Itasca.OpDispatch
