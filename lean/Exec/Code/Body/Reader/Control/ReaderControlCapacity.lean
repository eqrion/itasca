import Exec.Code.Body.Reader.Common.ReaderCapacity
import Exec.Code.Body.Reader.Control.ReaderReturn
import Exec.Code.Local.Relations.Common.SliceOpcodes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_block_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_block] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_block_capacity ops law before after out.core value called

theorem reader_loop_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_loop] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_loop_capacity ops law before after out.core value called

theorem reader_if_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_if] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_if_capacity ops law before after out.core value called

theorem reader_else_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_else] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_else_capacity ops law before after out.core value.2 called

theorem reader_end_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_end] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_end_capacity ops law before after out.core value.1 value.2 called

theorem reader_br_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_br_capacity ops law before after out.core value.1 value.2 called

theorem reader_br_if_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_br_if_capacity ops law before after out.core value.1 value.2 called

theorem reader_return_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_return_capacity ops law before after out.core  called

theorem reader_call_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 16#u8 before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_call] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_call_capacity ops law before after out.core value called
end Exec.Code
