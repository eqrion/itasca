import Exec.Code.Local.Callbacks.Calls.CallbackSafety
import Exec.Code.Local.Relations.Common.SelectLowering

/-! SELECT normal return from raw observed offsets. Polymorphic stacks and
rejected emission/observation outcomes require no final body certificate. -/
namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_operand_observed {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (values : List Itasca.code.StackType)
    (observed : ObservedStack compiler values) (depth : Usize)
    (positive : 0 < depth.val) (fits : depth.val ≤ values.length) :
    runtime.compiler.FunctionCompiler.operand ops compiler depth ⦃ out =>
      ∃ word, out = .Ok word ∧ word.val = compiler.function.local_slots.val +
        stackWords (values.take (values.length - depth.val)) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.operand
  have length := observed.length
  step with operand_at compiler.before.deref depth positive (by simpa [alloc.vec.Vec.deref, length] using fits)
    as ⟨out, exactValue⟩
  refine ⟨_, exactValue, ?_⟩
  simpa [alloc.vec.Vec.deref, length] using
    observed.get (values.length - depth.val) (by omega)

@[step] theorem finish_op_observed {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op
  step with compiler_emit ops law compiler instruction codeFits sourceFits coordinateFits as ⟨r, c, emitted⟩
  cases r with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact compiler_observe_stack ops law c state

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
@[step] theorem compiler_select_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (values : List Itasca.code.StackType) (typed : Bool)
    (observed : ObservedStack compiler values)
    (enough : compiler.reachable = true → 3 ≤ values.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have count := enough live
    obtain ⟨_, leftCall, left, rfl, leftValue⟩ := WP.spec_imp_exists
      (compiler_operand_observed ops compiler values observed 3#usize (by decide) (by simpa using count))
    obtain ⟨_, rightCall, right, rfl, rightValue⟩ := WP.spec_imp_exists
      (compiler_operand_observed ops compiler values observed 2#usize (by decide) (by simpa using (show 2 ≤ values.length by omega)))
    obtain ⟨_, condCall, condition, rfl, condValue⟩ := WP.spec_imp_exists
      (compiler_operand_observed ops compiler values observed 1#usize (by decide) (by simpa using (show 1 ≤ values.length by omega)))
    have ordered : left.val ≤ right.val := by
      rw [leftValue, rightValue]
      simpa using Nat.add_le_add_left (stackWords_take_mono values
        (a := values.length - 3) (b := values.length - 2) (by omega)) compiler.function.local_slots.val
    have sub : (right - left) ⦃ _ => True ⦄ := by step
    obtain ⟨difference, differenceCall, _⟩ := WP.spec_imp_exists sub
    rw [lower_select_eq ops compiler state left right condition difference typed live
      leftCall rightCall condCall differenceCall]
    exact finish_op_observed ops law compiler state _ codeFits sourceFits coordinateFits
  · have dead : runtime.compiler.lower.FunctionCompiler.op ops compiler state
        (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128 =
        runtime.compiler.FunctionCompiler.observe ops compiler state := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_neg live]
    rw [dead]
    exact compiler_observe_stack ops law compiler state

end Exec.Code
