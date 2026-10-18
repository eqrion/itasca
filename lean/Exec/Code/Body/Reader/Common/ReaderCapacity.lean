import Exec.Code.Local.Callbacks.Calls.CallbackCapacity
import Exec.Code.Local.Capacity.IntegerCapacity
import Exec.Code.Local.Capacity.LiteralCapacity
import Exec.Code.Body.Reader.Common.ReaderEqz
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_nop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_NOP before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_nop] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_nop_capacity ops law before after out called

theorem reader_unreachable_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_unreachable] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_unreachable_capacity ops law before after out called

theorem reader_drop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_DROP before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_drop] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_drop_capacity ops law before after out value called

theorem reader_i32_const_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_i32_const] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_i32_const_capacity ops law before after out value called

theorem reader_i64_const_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_i64_const] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_i64_const_capacity ops law before after out value called

theorem reader_local_get_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_local_get] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_local_get_capacity ops law before after out value called

theorem reader_local_set_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_local_set] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_local_set_capacity ops law before after out value called

theorem reader_local_tee_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_local_tee] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_local_tee_capacity ops law before after out value called

theorem reader_call_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_call] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_call_capacity ops law before after out value called

theorem reader_block_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BLOCK before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_block] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_block_capacity ops law before after out (Control.signature value) called

theorem reader_loop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOOP before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_loop] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_loop_capacity ops law before after out (Control.signature value) called

theorem reader_if_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_IF before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_if] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_if_capacity ops law before after out (Control.signature value) called

theorem reader_else_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_ELSE before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_else] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_else_capacity ops law before after out (Control.signature value) called

theorem reader_end_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_END before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_end] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_end_capacity ops law before after out value.1 (Control.signature value.2) called

theorem reader_br_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_br] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_br_capacity ops law before after out value.1 (Control.resultView value.2) called

theorem reader_br_if_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_IF before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_br_if] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_br_if_capacity ops law before after out value.1 (Control.resultView value.2) called

theorem reader_return_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_RETURN before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_return] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  exact compiler_return_capacity ops law before after out called

theorem reader_binary_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ty : Inn) (operation : IntegerBinary)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (binaryOpcode ty operation)) before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  obtain ⟨row, hook, meaning, handler, _, _, _, callback, _⟩ := binary_reader_facts ops before out ty operation
  rw [dispatch_numeric _ _ _ _ _ _ _ row hook meaning handler] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  rw [callback] at called
  exact compiler_integer_callback_capacity ops law before after out ty operation called

theorem reader_eqz_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ty : Inn)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (eqzOpcode ty)) before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  obtain ⟨row, hook, meaning, handler, _, _, _, callback, _⟩ := eqz_reader_facts ops before out ty
  rw [dispatch_numeric _ _ _ _ _ _ _ row hook meaning handler] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  rw [callback] at called
  exact compiler_eqz_callback_capacity ops law before after out ty called
end Exec.Code
