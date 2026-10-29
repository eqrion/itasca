import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringConditionalTransfer
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSafety
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget

/-!
Normal return of direct and conditional branch callbacks. The conditional proof covers underflow and empty/nonempty transfer cases before lifting to actual callback dispatch.
-/

/-! ## Branch If Safety -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Branch If Safety Complete -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## Branch Callback Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem branch_depth_target (frames : alloc.vec.Vec runtime.compiler.Frame) (depth : U32)
    (bound : depth.val < frames.val.length) :
    ∃ index : Usize, ∃ frame, frames.val[index.val]? = some frame ∧
      index.val + depth.val + 1 = frames.val.length := by
  let index := Usize.ofNatCore (frames.val.length-depth.val-1) (by
    have h := (alloc.vec.Vec.len frames).hBounds
    change frames.val.length < 2^UScalarTy.Usize.numBits at h
    omega)
  have inside : index.val < frames.val.length := by
    change frames.val.length-depth.val-1 < frames.val.length
    omega
  refine ⟨index,frames.val[index.val],by simp [inside],?_⟩
  change frames.val.length-depth.val-1+depth.val+1=frames.val.length
  omega

@[step] theorem compiler_br_callback_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (depthFits : depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length+2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth types ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  split
  · obtain ⟨index,frame,lookup,position⟩ := branch_depth_target compiler.frames depth depthFits
    step with compiler_branch_total ops law compiler frame index depth lookup position
      (fixups.lookup lookup (by omega)) codeFits sourceFits coordinate as ⟨status,after⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law {after with reachable := false} state
  · exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_br_if_callback_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (depthFits : depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (pcBound : compiler.function.code.val.length+3 < 2^32)
    (codeFits : compiler.function.code.val.length+3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+3 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth types ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  split
  · obtain ⟨index,frame,lookup,position⟩ := branch_depth_target compiler.frames depth depthFits
    step with compiler_branch_if_total_raw ops law compiler frame index depth lookup position
      (fixups.lookup lookup (by omega)) pcBound codeFits sourceFits coordinate as ⟨status,after⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law after state
  · exact compiler_observe_stack ops law compiler state
end Itasca.Runtime.Compiler

end
