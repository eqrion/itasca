import Exec.Code.Local.Relations.Control.BranchSkipForwardSafety
import Exec.Code.Local.Relations.Control.BranchSkipLoopSafety
import Exec.Code.Local.Callbacks.Calls.CallbackSafety
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem branch_skip_underflow_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (underflow : compiler.height.val <
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val + skip.val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ _ => True ⦄ := by
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

@[step] theorem compiler_branch_skip_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false ⦃ _ => True ⦄ := by
  by_cases loop : frame.kind = Itasca.code.LabelKind.Loop
  · by_cases enough : frame.params.val + skip.val ≤ compiler.height.val
    · let source := U32.ofNatCore (compiler.height.val - (frame.params.val + skip.val))
        (by have := compiler.height.hBounds; omega)
      have sourceValue : source.val + frame.params.val + skip.val = compiler.height.val := by
        change compiler.height.val - (frame.params.val + skip.val) + frame.params.val + skip.val = compiler.height.val
        omega
      by_cases empty : frame.params = 0#u32
      · apply WP.spec_mono (branch_elided_loop_with_skip ops law compiler frame index depth source skip
          lookup position loop (.inl empty) sourceValue (by omega) (by omega) coordinateFits)
        simp
      · by_cases same : source = frame.height
        · apply WP.spec_mono (branch_elided_loop_with_skip ops law compiler frame index depth source skip
            lookup position loop (.inr same) sourceValue (by omega) (by omega) coordinateFits)
          simp
        · apply WP.spec_mono (branch_transfer_loop_with_skip ops law compiler frame index depth source skip
            lookup position loop empty same sourceValue codeFits sourceFits coordinateFits)
          simp
    · exact branch_skip_underflow_total ops compiler frame index depth skip lookup position (by simp [loop]; omega)
  · by_cases enough : frame.results.val + skip.val ≤ compiler.height.val
    · let source := U32.ofNatCore (compiler.height.val - (frame.results.val + skip.val))
        (by have := compiler.height.hBounds; omega)
      have sourceValue : source.val + frame.results.val + skip.val = compiler.height.val := by
        change compiler.height.val - (frame.results.val + skip.val) + frame.results.val + skip.val = compiler.height.val
        omega
      by_cases empty : frame.results = 0#u32
      · apply WP.spec_mono (branch_elided_forward_with_skip ops law compiler frame index depth source skip
          lookup position loop (.inl empty) sourceValue fixupsFit (by omega) (by omega) coordinateFits)
        simp
      · by_cases same : source = frame.height
        · apply WP.spec_mono (branch_elided_forward_with_skip ops law compiler frame index depth source skip
            lookup position loop (.inr same) sourceValue fixupsFit (by omega) (by omega) coordinateFits)
          simp
        · apply WP.spec_mono (branch_transfer_forward_with_skip ops law compiler frame index depth source skip
            lookup position loop empty same sourceValue fixupsFit codeFits sourceFits coordinateFits)
          simp
    · exact branch_skip_underflow_total ops compiler frame index depth skip lookup position
        (by cases kindEq : frame.kind <;> simp_all)
end Exec.Code
