import Exec.Code.Body.Reader.Float.ReaderFloatConstantLowering
import Exec.Code.Local.Capacity.LiteralCapacity
import Exec.Code.Body.Reader.Common.ReaderLowering
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
theorem reader_f32_const_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_f32_const] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops before out value = _ at called
  rw [callback_float32_eq] at called
  exact compiler_op65_capacity ops law before after out _ _ _ called

theorem reader_f64_const_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rw [dispatch_f64_const] at accepted
  obtain ⟨value, _, called⟩ := reader_run_success _ _ _ _ _ accepted
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops before out value = _ at called
  rw [callback_float64_eq] at called
  exact compiler_op66_capacity ops law before after out _ _ _ called


theorem reader_f32_const_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F32_CONST before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index code.OP_F32_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) rfl accepted
  exact reader_f32_const_capacity ops law before after st.core out.core data env ctx run

theorem reader_f64_const_capacity_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_F64_CONST before = .ok (.Ok (), out, after)) :
    CapacityStep before after out.core := by
  obtain ⟨_,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index code.OP_F64_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) rfl accepted
  exact reader_f64_const_capacity ops law before after st.core out.core data env ctx run

end Exec.Code
