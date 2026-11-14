import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_copy_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (dst src count : U32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count ⦃ _ => True ⦄ := by
  exact runtime.compiler.FunctionCompiler.copy.total ops law compiler dst src count codeFits sourceFits coordinateFits

set_option maxRecDepth 4096 in
@[step] theorem compiler_local_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (offsetBound : index.val < compiler.local_offsets.val.length)
    (localBound : index.val < compiler.function.locals.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_get ops compiler state index 0#u32 0#u128 live
    rw [run]
    step as ⟨offsetIndex, offsetIndexValue⟩
    step as ⟨src, srcValue⟩
    step as ⟨localIndex, localIndexValue⟩
    step as ⟨ty, tyValue⟩
    step with compiler_width ty as ⟨count, countValue⟩
    step with compiler_copy_total ops law compiler compiler.height src count
      codeFits sourceFits coordinateFits as ⟨answer, nextCompiler⟩
    cases answer with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact compiler_observe_stack ops law nextCompiler state
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    exact compiler_observe_stack ops law compiler state

set_option maxRecDepth 4096 in
@[step] theorem compiler_local_write_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32) (tee : Bool)
    (offsetBound : index.val < compiler.local_offsets.val.length)
    (localBound : index.val < compiler.function.locals.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if tee then 34#u16 else 33#u16) index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run := runtime.compiler.lower.FunctionCompiler.op.local_set_or_tee ops compiler state tee index 0#u32 0#u128 live
    rw [run]
    step as ⟨offsetIndex, offsetIndexValue⟩
    step as ⟨dst, dstValue⟩
    step with compiler_operand_total ops compiler 1#usize as ⟨operandResult, _⟩
    cases operandResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok src =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨localIndex, localIndexValue⟩
      step as ⟨ty, tyValue⟩
      step with compiler_width ty as ⟨count, countValue⟩
      step with compiler_copy_total ops law compiler dst src count
        codeFits sourceFits coordinateFits as ⟨answer, nextCompiler⟩
      cases answer with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        exact compiler_observe_stack ops law nextCompiler state
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Compiler
