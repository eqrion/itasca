import Exec.Code.Local.Callbacks.Table.CompilerTableScratchLiteral
import Exec.Code.Local.Callbacks.Table.CompilerTableScratchCallbacks
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 0#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_unreachable (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_unreachable_depths ops law before after out.core callback

theorem reader_nop_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 1#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 1#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_nop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_nop_depths ops law before after out.core callback

theorem reader_return_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  cases value
  exact compiler_return_depths ops law before after out.core callback

theorem reader_call_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 16#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  rw [Wasm2.CallbackTrace.dispatch_call] at accepted
  obtain ⟨value,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_call_depths ops law before after out.core value callback

theorem reader_drop_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 26#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 26#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_drop_depths ops law before after out.core value callback

theorem reader_local_get_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 32#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 32#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_local_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_local_get_depths ops law before after out.core value callback

theorem reader_local_set_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 33#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 33#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_local_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_local_set_depths ops law before after out.core value callback

theorem reader_local_tee_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 34#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 34#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_local_tee (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_local_tee_depths ops law before after out.core value callback

theorem reader_i32_const_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 65#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 65#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_i32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_i32_const_depths ops law before after out.core value callback

theorem reader_i64_const_depths_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 66#u8 before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 66#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_i64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact compiler_i64_const_depths ops law before after out.core value callback
end Exec.Code
