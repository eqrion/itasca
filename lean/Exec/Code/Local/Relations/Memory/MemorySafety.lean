import Exec.Code.Local.Lowering.Common.NumericSafety
import Exec.Code.Local.Relations.Memory.MemoryLowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_memory_load_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Memory.Load) (offset alignment : U32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (memoryLoadOpcode op) offset alignment 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_memory_load_dispatch ops compiler state op offset alignment live]
    unfold memoryLoadLowering
    step with compiler_operand_total ops compiler 1#usize as ⟨answer, _⟩
    cases answer with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok word =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        memoryLoadInstruction_make, core.option.Option.ok_or]
      exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_memory_store_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Memory.Store) (offset alignment : U32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (memoryStoreOpcode op) offset alignment 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · rw [lower_memory_store_dispatch ops compiler state op offset alignment live]
    unfold memoryStoreLowering
    step with compiler_operand_total ops compiler 2#usize as ⟨addressResult, _⟩
    cases addressResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok address =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_operand_total ops compiler 1#usize as ⟨valueResult, _⟩
      cases valueResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          memoryStoreInstruction_make, core.option.Option.ok_or]
        exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state
end Itasca.Runtime.Code
