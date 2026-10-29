import Itasca.Runtime.Compiler.Local.Relations.Operations.PairSafety
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowering

/-!
Normal return of plain and complete stateful compiler callbacks.

Main declarations: `compiler_stateful_plain_total` and `compiler_stateful_total`. A direct consumer is `Compiler.Body.Reader.Safety.BulkSafety`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_stateful_plain_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32)
    (plain : statefulUsesPair op = false)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (statefulOpcode op) a b 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_stateful_dispatch ops compiler state op a b live]
    cases op <;> simp only [statefulUsesPair, Bool.true_eq_false] at plain
    all_goals simp only [statefulLowering]
    all_goals try exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
    all_goals
      step with compiler_operand_total ops compiler _ as ⟨answer, _⟩
      cases answer with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok word =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        first
        | exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
        | step with compiler_operand_total ops compiler _ as ⟨secondAnswer, _⟩
          cases secondAnswer with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok secondWord =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state
@[step] theorem compiler_stateful_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Stateful.Instruction) (a b : U32)
    (pairFits : compiler.function.indirect.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (statefulOpcode op) a b 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases plain : statefulUsesPair op = false
  · exact compiler_stateful_plain_total ops law compiler state op a b plain codeFits sourceFits coordinateFits
  · by_cases live : compiler.reachable = true
    · rw [lower_stateful_dispatch ops compiler state op a b live]
      cases op <;> simp only [statefulUsesPair, Bool.false_eq_true, not_true_eq_false] at plain
      all_goals simp only [statefulLowering]
      all_goals
        step with compiler_pair_total ops law compiler a b pairFits
          as ⟨pairResult, paired, budget, pairs, pairEq⟩
        subst paired
        cases pairResult with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok entry =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with compiler_operand_total ops _ 3#usize as ⟨operandResult, _⟩
          cases operandResult with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok first =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            exact finish_op_observed ops law _ state _ codeFits sourceFits coordinateFits
    · unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_neg live]
      exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Code
