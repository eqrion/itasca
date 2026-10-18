import Exec.Code.Body.Callbacks.Common.CompilerPrefixTerminal
import Exec.Code.Local.Control.Control.UniversalLoopBranch
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem CompilerPrefix.branch_loop {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (dead : after.reachable = false)
    (ordinary : CompilerOrdinaryStable before after)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count : U32)
    (found : before.frames.val[index]? = some frame) (isLoop : frame.kind = .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count frame.start_pc)
    (known : ConcreteStack nextRaw) (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames)
    (branchInstructions dst src count frame.start_pc) codeEq (by rw [ordinary.controls])).advance (.BR (.mk_uN depth))
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchInstructions
    split <;> simp
  exact ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance (.BR (.mk_uN depth)),
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance (.BR (.mk_uN depth)), known,
    .terminal dead entered (retained.branch_loop frame index depth scope dst src count found framePosition isLoop
      scopeAt discarded stackEq destination source width codeEq ordinary.frames localsEq),
    invariant.arms.append retained.sites (branchInstructions dst src count frame.start_pc) (.BR (.mk_uN depth)) codeEq ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩

theorem CompilerPrefix.branch_if_loop {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition stack}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (ordinary : CompilerOrdinaryStable before after)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count condition resume : U32)
    (found : before.frames.val[index]? = some frame) (isLoop : frame.kind = .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (inputStack : Sequence.stackTypes raw = stack ++ [.I32])
    (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count frame.start_pc condition resume)
    (sourceTypes : SourceStack nextRaw stack) (layout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack) (resumePosition : resume.val = after.function.code.val.length) (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.extend (congrArg (fun fs => fs.val) ordinary.frames)
    (branchIfInstructions dst src count frame.start_pc condition resume) codeEq (by rw [ordinary.controls])).advance (.BR_IF (.mk_uN depth))
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchIfInstructions
    split <;> simp
  refine ⟨invariant.metadata.trans ordinary.stable, frames, invariant.entryChain.advance (.BR_IF (.mk_uN depth)),
    (by simpa only [ordinary.frames] using invariant.dormant), invariant.conditions.advance (.BR_IF (.mk_uN depth)), sourceTypes.concrete,
    .live live entered ?_,
    invariant.arms.append retained.sites (branchIfInstructions dst src count frame.start_pc condition resume) (.BR_IF (.mk_uN depth)) codeEq ordinary.frames,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) ordinary.controls)
      (by rw [ordinary.frames])).advance (Nat.le_of_lt consumed), cursor⟩
  have next := (inputStack ▸ retained).branch_if_loop frame index depth scope dst src count condition resume
    found framePosition isLoop scopeAt discarded stackEq destination source width codeEq ordinary.frames localsEq
    layout conditionSlot resumePosition
  simpa only [sourceTypes.decoded] using next

end Exec.Code
