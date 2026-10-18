import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneTactic
import Exec.Code.Local.Lowering.Common.NumericEffects
import Exec.Code.Local.Lowering.Float.FloatEffects
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_numeric_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Numeric.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_numeric_dispatch ops before state op reach] at accepted
    unfold numericLowering at accepted
    repeat' code_mono_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_float_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Float.Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' code_mono_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

theorem compiler_core_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' code_mono_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted

end Exec.Code
