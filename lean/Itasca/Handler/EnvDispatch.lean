import Itasca.Handler.EnvCalls
import Itasca.Binary.Wasm1.MemoryTyping
import Itasca.Visitor.Basic
import Itasca.Visitor.Total

/-!
# Environment instruction dispatch

For each variable, call and memory instruction, `code.step` on its opcode equals running the
corresponding reader and then the visitor's hook through `CoreVisitor.run`
(`code.step_local_get.dispatch`, ..., `code.step_memory_grow.dispatch`).
`code.step_memory.dispatch` does the same for loads and stores, selected by `MemoryMeaning`.
-/

open Aeneas Aeneas.Std

namespace Itasca

theorem code.step_local_get.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_GET v =
      CoreVisitor.run (code.read_local_get st data ctx) visitor.on_local_get v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_local_set.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_SET v =
      CoreVisitor.run (code.read_local_set st data ctx) visitor.on_local_set v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_local_tee.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_TEE v =
      CoreVisitor.run (code.read_local_tee st data ctx) visitor.on_local_tee v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_global_get.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_GET v =
      CoreVisitor.run (code.read_global_get st data env) visitor.on_global_get v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_global_set.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_SET v =
      CoreVisitor.run (code.read_global_set st data env) visitor.on_global_set v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_memory_size.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_SIZE v =
      CoreVisitor.run (code.read_memory_size st data env) (fun v s _ => visitor.on_memory_size v s) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem code.step_memory_grow.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_GROW v =
      CoreVisitor.run (code.read_memory_grow st data env) (fun v s _ => visitor.on_memory_grow v s) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- For an opcode with a row in `MemoryMeaning.opcodeMeaning`, `code.step` runs `code.read_store`
or `code.read_load` and then `code.visit_memory`. -/
theorem code.step_memory.dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run
        (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
          else code.read_load st data env operation.ty operation.naturalAlign)
        (fun v s arg => code.visit_memory visitor v s opcode arg) v := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  unfold MemoryMeaning.opcodeMeaning at hrow
  dsimp only [UScalar.val, BitVec.toNat] at hrow
  split at hrow <;> cases hrow
  all_goals have heqval (a b : U8) : a = b ↔ a.val = b.val := ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
  all_goals simp [global_simps, CoreVisitor.run,
    MemoryMeaning.fullLoad, MemoryMeaning.fullStore, MemoryMeaning.packedLoad, MemoryMeaning.packedStore,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, *]
  all_goals congr 1
  all_goals funext x
  all_goals obtain ⟨res, s⟩ := x
  all_goals cases res <;> simp
  all_goals congr 1

end Itasca
