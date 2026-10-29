import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowering
import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSuccess
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessEmit

/-!
Acceptance of either pair-based callback exposes its actual allocation.

Main declarations: `lower_stateful_pair_success` and `compiler_finish_indirect`. A direct consumer is `Compiler.Local.Relations.Calls.IndirectCallLowering`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Acceptance of either pair-based callback exposes its actual allocation. -/
theorem lower_stateful_pair_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Stateful.Instruction) (a b : U32)
    (reachable : before.reachable = true) (pairOpcode : statefulUsesPair op = true)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (), after)) :
    ∃ entry paired, runtime.compiler.FunctionCompiler.pair ops before a b = .ok (.Ok entry, paired) := by
  rw [lower_stateful_dispatch ops before state op a b reachable] at accepted
  cases op <;> simp only [statefulUsesPair, Bool.false_eq_true] at pairOpcode
  all_goals
    simp only [statefulLowering] at accepted
    obtain ⟨⟨result,paired⟩,pair,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok entry => exact ⟨entry,paired,pair⟩

/-- Finishing an ordinary instruction preserves the immutable pair table. -/
theorem compiler_finish_indirect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (), after)) :
    after.function.indirect = before.function.indirect := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    have frame := compiler_observe_frame ops law middle state
    rw [rest,WP.spec_ok] at frame
    change ObserveFrame middle after at frame
    have same : after.function.indirect = middle.function.indirect := by rw [frame]
    obtain ⟨budget,code,sources,rfl,_,_⟩ := compiler_emit_success ops law before middle instruction emitted
    exact same

end Itasca.Runtime.Code
