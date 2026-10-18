import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Calls.FixupCallbacks
import Exec.Code.Body.Reader.Common.ReaderLiteralCodeMonotone
import Exec.Code.Local.Callbacks.Common.FixupPreservation
import Exec.Code.Local.Callbacks.Common.CompilerTerminalMetadata
import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneLiteral
import Exec.Code.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Calls.ReaderWasm2Call
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_unreachable_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 0#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_unreachable (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact compiler_unreachable_fixup_budget ops law before after out.core budget callback

theorem reader_nop_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 1#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 1#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_nop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases value
  exact budget.ordinary (compiler_nop_ordinary_result ops law before after out.core (.Ok ()) callback)
    (compiler_nop_code_mono ops law before after out.core callback)

theorem reader_return_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  cases value
  exact budget.ordinary (compiler_return_ordinary_result ops law before after out.core (.Ok ()) callback)
    (compiler_return_code_mono ops law before after out.core callback)

theorem reader_call_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 16#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  rw [Wasm2.CallbackTrace.dispatch_call] at accepted
  obtain ⟨value,read,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact budget.ordinary (compiler_call_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_call_code_mono ops law before after out.core value callback)

theorem reader_drop_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 26#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 26#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_drop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact budget.ordinary (compiler_drop_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_drop_code_mono ops law before after out.core value callback)

theorem reader_local_get_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 32#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 32#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_local_get (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact budget.ordinary (compiler_local_get_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_local_get_code_mono ops law before after out.core value callback)

theorem reader_local_set_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 33#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 33#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_local_set (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact budget.ordinary (compiler_local_set_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_local_set_code_mono ops law before after out.core value callback)

theorem reader_local_tee_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 34#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 34#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_local_tee (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact budget.ordinary (compiler_local_tee_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_local_tee_code_mono ops law before after out.core value callback)

theorem reader_i32_const_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 65#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 65#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_i32_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact budget.ordinary (compiler_i32_const_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_i32_const_code_mono ops law before after out.core value callback)

theorem reader_i64_const_fixup_budget_wasm2 {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 66#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index 66#u8 before after
    (by decide) (by decide) (by rfl) (by simp only [global_simps]; decide) rfl accepted
  have dispatch := dispatch_i64_const (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st.core data env ctx before
  simp only [global_simps] at dispatch
  rw [dispatch] at run
  obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
  exact budget.ordinary (compiler_i64_const_ordinary_result ops law before after out.core value (.Ok ()) callback)
    (compiler_i64_const_code_mono ops law before after out.core value callback)
end Exec.Code
