import Exec.Code.Local.Lowering.Common.LoweringConditionalTransfer
import Exec.Code.Local.Callbacks.Calls.CallbackSafety
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem branch_if_underflow_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (underflow : compiler.height.val <
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + 1) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  cases kindEq : frame.kind
  all_goals simp only [kindEq] at underflow
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch
    step as ⟨last, lastValue⟩
    step as ⟨d, dValue⟩
    step as ⟨actualIndex, indexValue⟩
    have indexEq : actualIndex = index := by
      apply UScalar.eq_of_val_eq
      simp [alloc.vec.Vec.len] at lastValue
      scalar_tac
    subst actualIndex
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    step as ⟨found, foundValue⟩
    have foundEq : found = frame := foundValue.trans (List.getElem?_eq_some_iff.mp lookup).2
    rw [foundEq]
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true]
    step as ⟨sum, sumValue⟩
    cases sum with
    | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some sum =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨source, sourceValue⟩
      cases source with
      | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some source => simp at sumValue sourceValue; omega

@[step] theorem compiler_branch_if_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (pcBound : compiler.function.code.val.length + 3 < 2^32)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  let resume : U32 := UScalar.ofNatCore (compiler.function.code.val.length + 3) pcBound
  by_cases loop : frame.kind = .Loop
  · by_cases enough : frame.params.val + 1 ≤ compiler.height.val
    · let source : U32 := UScalar.ofNatCore (compiler.height.val - (frame.params.val + 1)) (by scalar_tac)
      have sourcePosition : source.val + frame.params.val + 1 = compiler.height.val := by
        change compiler.height.val - (frame.params.val + 1) + frame.params.val + 1 = compiler.height.val
        omega
      by_cases elided : frame.params = 0#u32 ∨ source = frame.height
      · exact WP.spec_mono (branch_if_elided_loop ops law compiler frame index depth source condition
          lookup position loop elided sourcePosition conditionAt (by omega) (by omega) coordinateFits) (by simp)
      · have nonempty : frame.params ≠ 0#u32 := fun h => elided (.inl h)
        have different : source ≠ frame.height := fun h => elided (.inr h)
        exact WP.spec_mono (branch_if_transfer_loop ops law compiler frame index depth source condition resume
          lookup position loop nonempty different sourcePosition conditionAt rfl codeFits sourceFits coordinateFits) (by simp)
    · exact branch_if_underflow_total ops compiler frame index depth lookup position (by simp [loop]; omega)
  · by_cases enough : frame.results.val + 1 ≤ compiler.height.val
    · let source : U32 := UScalar.ofNatCore (compiler.height.val - (frame.results.val + 1)) (by scalar_tac)
      have sourcePosition : source.val + frame.results.val + 1 = compiler.height.val := by
        change compiler.height.val - (frame.results.val + 1) + frame.results.val + 1 = compiler.height.val
        omega
      by_cases elided : frame.results = 0#u32 ∨ source = frame.height
      · exact WP.spec_mono (branch_if_elided_forward ops law compiler frame index depth source condition
          lookup position loop elided sourcePosition conditionAt fixupsFit (by omega) (by omega) coordinateFits) (by simp)
      · have nonempty : frame.results ≠ 0#u32 := fun h => elided (.inl h)
        have different : source ≠ frame.height := fun h => elided (.inr h)
        exact WP.spec_mono (branch_if_transfer_forward ops law compiler frame index depth source condition resume
          lookup position loop nonempty different sourcePosition conditionAt rfl fixupsFit codeFits sourceFits coordinateFits) (by simp)
    · exact branch_if_underflow_total ops compiler frame index depth lookup position (by cases kindEq : frame.kind <;> simp_all)

end Exec.Code
