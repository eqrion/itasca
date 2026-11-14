import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend

/-!
Fixup-budget preservation through ordinary and control callbacks.

Main declarations: `FixupBudget.ordinary` and `compiler_end_fixup_budget`. A direct consumer is `Compiler.Local.Callbacks.Control.FixupBranchPreservation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096

theorem FixupBudget.ordinary {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (stable : CompilerOrdinaryStable before after)
    (growth : before.function.code.val.length ≤ after.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  rw [stable.frames]
  exact budget.mono growth

private theorem index_frame {T : Type} {frames : alloc.vec.Vec T} {index frame back}
    (called : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T)
      frames index = .ok (frame, back)) :
    frames.val[index.val]? = some frame ∧ back = fun value => frames.set index value := by
  rw [alloc.vec.Vec.index_mut_slice_index] at called
  unfold alloc.vec.Vec.index_mut_usize at called
  obtain ⟨value, selected, rest⟩ := bind_ok_inv _ _ _ called
  simp only [Result.ok.injEq, Prod.mk.injEq] at rest
  obtain ⟨rfl, rfl⟩ := rest
  unfold alloc.vec.Vec.index_usize at selected
  split at selected
  · simp [Result.fail] at selected
  · rename_i found lookup
    cases Result.ok_injective selected
    exact ⟨lookup, rfl⟩

private theorem push_fixup {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.Budget.push ops budget before value = .ok (status,afterBudget,after)) :
    status = .Ok () → after.val = before.val ++ [value] := by
  intro same; subst status
  exact (budget_push_success ops law budget afterBudget before after value accepted).2

private theorem popped_frames {frames : alloc.vec.Vec runtime.compiler.Frame} {value after}
    (called : alloc.vec.Vec.pop Global frames = .ok (value, after)) :
    after.val = frames.val.dropLast := by
  simp only [alloc.vec.Vec.pop, Result.ok.injEq, Prod.mk.injEq] at called
  rw [← called.2, alloc.vec.Vec.from_val]

open Lean Meta Elab Tactic in
elab "fixup_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not equation"
  let some fn := lhs.getAppFn.constName? | throwError "not named"
  match fn with
  | ``alloc.vec.Vec.pop =>
    evalTactic (← `(tactic| have poppedFrame := popped_frames $h))
  | ``alloc.vec.Vec.index_mut =>
    evalTactic (← `(tactic| obtain ⟨selectedFrame, restoredFrame⟩ := index_frame $h))
    evalTactic (← `(tactic| have frameMember := List.mem_of_getElem? (index_frame $h).1))
  | ``runtime.compiler.Budget.push =>
    evalTactic (← `(tactic| have pushedFrame := push_fixup $ops $law _ _ _ _ _ _ $h))
  | _ =>
    let tac ← match fn with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have framesEq := (compiler_observe_ordinary_result $ops $law _ _ _ _ $h).frames)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have framesEq := (compiler_emit_ordinary_result $ops _ _ _ _ $h).frames)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have framesEq := (compiler_copy_ordinary_result $ops _ _ _ _ _ _ $h).frames)
    | ``runtime.compiler.FunctionCompiler.pc =>
      `(tactic| have framesEq := (compiler_pc_ordinary_result $ops _ _ _ $h).frames)
    | ``runtime.compiler.control.FunctionCompiler.patch =>
      `(tactic| have framesEq := (compiler_patch_ordinary_result $ops _ _ _ _ _ $h).frames)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 =>
      `(tactic| have framesEq := (compiler_fixups_ordinary_result $ops _ _ _ _ _ _ $h).frames)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 =>
      `(tactic| have framesEq := (compiler_fixups_after_if_ordinary_result $ops _ _ _ _ _ _ $h).frames)
    | _ => throwError "not a frames helper"
    evalTactic tac
    evalTactic (← `(tactic| try code_mono_effect $h using $ops, $law))



theorem compiler_enter_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind bt (.Ok ()) accepted).2.2 rfl
  have publication := publish law
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  rw [observedFrame]
  change FixupBudget middle.frames.val middle.function.code.val.length
  rw [publication.frames]
  intro frame member
  rcases List.mem_append.mp member with old | fresh
  · have original := budget frame old
    rw [publication.code, List.length_append]
    omega
  · simp only [List.mem_singleton] at fresh
    subst frame
    change 0 ≤ middle.function.code.val.length
    omega


theorem compiler_end_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind bt = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind bt (.Ok ()) accepted
  obtain ⟨frame, remaining, popped, frames, length, sources⟩ := effect.sources_frames law
  have remainingEq := popped_frames popped
  intro retained member
  rw [frames, remainingEq] at member
  exact (budget retained (List.mem_of_mem_dropLast member)).trans (by omega)

end Itasca.Runtime.Compiler
