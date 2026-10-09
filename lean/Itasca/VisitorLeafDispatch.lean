import Itasca.VisitorEventTables
import Itasca.EnvDispatch
import Itasca.Select
import Itasca.AllNumeric

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

theorem dispatch_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v =
      CoreVisitor.run (.ok (.Ok (), st)) (fun v s _ => invoke visitor v (.op s (.nop))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1

theorem dispatch_unreachable {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      CoreVisitor.run (code.read_unreachable st) (fun v s _ => invoke visitor v (.op s (.unreachable))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem dispatch_drop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      CoreVisitor.run (code.read_drop st) (fun v s a => invoke visitor v (.op s (.drop a))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem dispatch_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      CoreVisitor.run (code.read_i32_const st data) (fun v s a => invoke visitor v (.op s (.i32_const a))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem dispatch_i64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) (fun v s a => invoke visitor v (.op s (.i64_const a))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem dispatch_f32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) (fun v s a => invoke visitor v (.op s (.f32_const a))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem dispatch_f64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) (fun v s a => invoke visitor v (.op s (.f64_const a))) v := by
  simp [global_simps, CoreVisitor.run, invoke, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

theorem dispatch_select {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      CoreVisitor.run (code.read_select st) (fun v s a => invoke visitor v (.op s (.select a))) v :=
  code.step_select.dispatch visitor st data env ctx v

theorem dispatch_local_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_GET v =
      CoreVisitor.run (code.read_local_get st data ctx) (fun v s a => invoke visitor v (.op s (.local_get a))) v :=
  code.step_local_get.dispatch visitor st data env ctx v

theorem dispatch_local_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_SET v =
      CoreVisitor.run (code.read_local_set st data ctx) (fun v s a => invoke visitor v (.op s (.local_set a))) v :=
  code.step_local_set.dispatch visitor st data env ctx v

theorem dispatch_local_tee {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_TEE v =
      CoreVisitor.run (code.read_local_tee st data ctx) (fun v s a => invoke visitor v (.op s (.local_tee a))) v :=
  code.step_local_tee.dispatch visitor st data env ctx v

theorem dispatch_global_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_GET v =
      CoreVisitor.run (code.read_global_get st data env) (fun v s a => invoke visitor v (.op s (.global_get a))) v :=
  code.step_global_get.dispatch visitor st data env ctx v

theorem dispatch_global_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_SET v =
      CoreVisitor.run (code.read_global_set st data env) (fun v s a => invoke visitor v (.op s (.global_set a))) v :=
  code.step_global_set.dispatch visitor st data env ctx v

theorem dispatch_call {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_CALL v =
      CoreVisitor.run (code.read_call st data env) (fun v s a => invoke visitor v (.op s (.call a))) v :=
  code.step_call.dispatch visitor st data env ctx v

theorem dispatch_call_indirect {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_CALL_INDIRECT v =
      CoreVisitor.run (code.read_call_indirect st data env) (fun v s a => invoke visitor v (.op s (.call_indirect a))) v :=
  code.step_call_indirect.dispatch visitor st data env ctx v

theorem dispatch_memory_size {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_SIZE v =
      CoreVisitor.run (code.read_memory_size st data env) (fun v s _ => invoke visitor v (.op s (.memory_size))) v :=
  code.step_memory_size.dispatch visitor st data env ctx v

theorem dispatch_memory_grow {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_GROW v =
      CoreVisitor.run (code.read_memory_grow st data env) (fun v s _ => invoke visitor v (.op s (.memory_grow))) v :=
  code.step_memory_grow.dispatch visitor st data env ctx v

theorem dispatch_numeric {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : Numeric.Operation) (hook : NumericHook)
    (hrow : Numeric.opcodeMeaning opcode = some operation)
    (hhook : NumericHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run (Numeric.read operation st)
        (fun v s (_ : Unit) => invoke visitor v (.op s (.numeric hook))) v := by
  rw [code.step.numeric_dispatch visitor st data env ctx opcode v (Numeric.NumericOp.bounds hrow).1,
    code.step_numeric.dispatch visitor st opcode operation v hrow]
  simp only [visit_numeric, hhook]

theorem dispatch_memory {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : MemoryMeaning.Operation) (hook : MemoryHook)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation)
    (hhook : MemoryHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run
        (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
          else code.read_load st data env operation.ty operation.naturalAlign)
        (fun v s arg => invoke visitor v (.op s (.memory hook arg))) v := by
  rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hrow]
  simp only [visit_memory, hhook]

end Itasca.VisitorTrace
