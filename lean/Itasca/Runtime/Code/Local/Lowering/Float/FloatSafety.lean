import Itasca.Runtime.Code.Local.Lowering.Common.NumericSafety
import Itasca.Runtime.Code.Local.Lowering.Float.FloatLowering

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_float_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Float.Instruction)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (floatOpcode op) 0#u32 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_float_dispatch ops compiler state op live]
    unfold floatLowering
    rw [floatOpcode_binary]
    simp only [bind_ok]
    have depthEq : (if decide (op.arity = 2) = true then Result.ok 2#usize else Result.ok 1#usize) =
        Result.ok (floatDepth op) := by simp [floatDepth]; split <;> rfl
    rw [depthEq, bind_ok]
    step with compiler_operand_total ops compiler _ as ⟨leftResult, _⟩
    cases leftResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok left =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_operand_total ops compiler 1#usize as ⟨rightResult, _⟩
      cases rightResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok right =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          floatInstruction_make, core.option.Option.ok_or]
        exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · have dead : runtime.compiler.lower.FunctionCompiler.op ops compiler state
        (floatOpcode op) 0#u32 0#u32 0#u128 =
        runtime.compiler.FunctionCompiler.observe ops compiler state := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_neg live]
    rw [dead]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Code
