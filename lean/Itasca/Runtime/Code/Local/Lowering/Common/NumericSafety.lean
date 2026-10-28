import Itasca.Runtime.Code.Local.Relations.Common.SelectSafety
import Itasca.Runtime.Code.Local.Lowering.Common.NumericLowering

/-! Integer lowering returns normally even for missing operands. Only emission
capacity and source-coordinate bounds are required; operand errors remain
ordinary visitor errors. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_operand_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (depth : Usize) :
    runtime.compiler.FunctionCompiler.operand ops compiler depth ⦃ out =>
      ∀ word, out = .Ok word → word ∈ compiler.before.val ⦄ := by
  simpa [runtime.compiler.FunctionCompiler.operand, alloc.vec.Vec.deref] using
    operand_at_total compiler.before.deref depth

@[step] theorem compiler_numeric_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Numeric.Instruction)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (integerOpcode op) 0#u32 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_numeric_dispatch ops compiler state op live]
    unfold numericLowering
    rw [integerOpcode_binary]
    simp only [bind_ok]
    have depthEq : (if decide (op.arity = 2) = true then Result.ok 2#usize else Result.ok 1#usize) =
        Result.ok (integerDepth op) := by simp [integerDepth]; split <;> rfl
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
          integerInstruction_make, core.option.Option.ok_or]
        exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · have dead : runtime.compiler.lower.FunctionCompiler.op ops compiler state
        (integerOpcode op) 0#u32 0#u32 0#u128 =
        runtime.compiler.FunctionCompiler.observe ops compiler state := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_neg live]
    rw [dead]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Code
