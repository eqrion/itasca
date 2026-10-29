import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneTactic
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowering
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallLowering

/-!
Emitted-code monotonicity of stateful and indirect-call callbacks.

Main declarations: `compiler_stateful_code_mono` and `compiler_indirect_call_code_mono`. A direct consumer is `Compiler.Local.Publication.LiteralMapPublication`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_stateful_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' code_mono_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_code_mono ops law before after state status accepted
theorem compiler_indirect_call_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    unfold indirectCallLowering at accepted
    repeat' code_mono_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_code_mono ops law before after state status accepted
end Itasca.Runtime.Code
