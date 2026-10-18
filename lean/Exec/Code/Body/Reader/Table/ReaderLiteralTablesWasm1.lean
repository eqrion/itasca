import Exec.Code.Local.Lowering.Table.LiteralTablePreservation
import Exec.Code.Local.Callbacks.Table.CallbackTables
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 0#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_unreachable (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_unreachable_tables ops law before after out callback

theorem reader_nop_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 1#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_nop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_nop_tables ops law before after out callback

theorem reader_return_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 15#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have dispatch := VisitorTrace.dispatch_return (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  cases value
  exact compiler_return_tables ops law before after out callback

theorem reader_call_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 16#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have dispatch := VisitorTrace.dispatch_call (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at accepted
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_call_tables ops law before after out value callback

theorem reader_drop_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 26#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_drop_tables ops law before after out value callback

theorem reader_local_get_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 32#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_local_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_local_get_tables ops law before after out value callback

theorem reader_local_set_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 33#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_local_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_local_set_tables ops law before after out value callback

theorem reader_local_tee_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 34#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_local_tee (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_local_tee_tables ops law before after out value callback

theorem reader_i32_const_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 65#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_i32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_i32_const_tables ops law before after out value callback

theorem reader_i64_const_tables_wasm1 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 66#u8 before = .ok (.Ok (),out,after)) :
    CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  have run := accepted
  have dispatch := dispatch_i64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_i64_const_tables ops law before after out value callback
end Exec.Code
