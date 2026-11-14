import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_operand_height {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (values : List Itasca.code.StackType)
    (observed : ObservedStack compiler values) (depth : Usize) :
    runtime.compiler.FunctionCompiler.operand ops compiler depth ⦃ out =>
      ∀ word, out = .Ok word → word.val ≤ compiler.height.val ⦄ := by
  apply WP.spec_mono (compiler_operand_total ops compiler depth)
  intro out member word success
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp (member word success)
  rw [← equal]
  exact observed.operand_le_height index bound

set_option maxRecDepth 4096 in
@[step] theorem compiler_global_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨wide, top, _⟩ := WP.spec_imp_exists (top_is_v128_total state.vals.deref)
    rw [lower_global_get_eq ops compiler state index wide live top]
    exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    exact compiler_observe_stack ops law compiler state

set_option maxRecDepth 4096 in
@[step] theorem compiler_global_set_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32) (values : List Itasca.code.StackType)
    (observed : ObservedStack compiler values)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128 =
        globalSetLowering ops compiler state index := by
      exact runtime.compiler.lower.FunctionCompiler.op.global_set ops compiler state index 0#u32 0#u128 live
    rw [dispatch]
    unfold globalSetLowering
    step with compiler_operand_height ops compiler values observed 1#usize as ⟨answer, bound⟩
    cases answer with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok word =>
      have safe := bound word rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨difference, differenceEq⟩
      split <;> simp only [bind_ok] <;>
        exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true live)]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Compiler
