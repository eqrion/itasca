import Exec.Code.Local.Relations.Control.BranchIfSafety
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
private theorem branch_if_empty_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (empty : compiler.before.val = []) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  cases kindEq : frame.kind
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
      | some source =>
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          runtime.compiler.FunctionCompiler.operand, runtime.compiler.operand_at,
          alloc.vec.Vec.deref, Slice.len, empty,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem compiler_branch_if_total_raw {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (pcBound : compiler.function.code.val.length + 3 < 2^32)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ _ => True ⦄ := by
  by_cases empty : compiler.before.val = []
  · exact branch_if_empty_total ops compiler frame index depth lookup position empty
  · have positive : 0 < compiler.before.val.length := List.length_pos_iff.mpr empty
    let condition := compiler.before.val[compiler.before.val.length-1]
    have conditionAt : compiler.before.val[compiler.before.val.length-1]? = some condition := by
      simp [condition,show compiler.before.val.length-1 < compiler.before.val.length by omega]
    exact compiler_branch_if_total ops law compiler frame index depth condition lookup position conditionAt
      fixupsFit pcBound codeFits sourceFits coordinateFits
end Exec.Code
