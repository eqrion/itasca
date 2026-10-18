import Exec.Code.Local.Capacity.AuxiliaryGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_stateful_auxiliary_growth {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after)) :
    AuxiliaryGrowth before after := by
  by_cases live : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b live] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' auxiliary_growth_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg live] at accepted
    exact .of_tables (compiler_observe_tables ops law before after state (.Ok ()) accepted)
      (compiler_observe_code_mono ops law before after state (.Ok ()) accepted)
end Exec.Code
