import Exec.Code.Body.Callbacks.Common.CompilerPrefixTerminal
import Exec.Code.Local.Control.Control.UniversalLoopBranch
import Exec.Code.Local.Callbacks.Control.ElseBranches
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A forward branch carries the complete compiler invariant into terminal
source mode, retaining its selected scope and its actual appended fixup. -/
theorem CompilerPrefix.branch_forward {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (dead : after.reachable = false)
    (stable : CompilerStable before after) (maps : after.function.controls = before.function.controls)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame) (forward : frame.kind ≠ .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count old)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (known : ConcreteStack nextRaw) (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.record_branch index frame fixups found forward framesEq
    (fun _ _ shape => shape.extend (branchInstructions dst src count old) codeEq (by rw [maps]))).advance (.BR (.mk_uN depth))
  have clean : DormantFrames after.frames.val := by
    rw [framesEq]
    exact invariant.frames.record_branch_dormant invariant.entryChain entered invariant.dormant index frame fixups found
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchInstructions
    split <;> simp
  exact ⟨invariant.metadata.trans stable, frames, invariant.entryChain.advance (.BR (.mk_uN depth)), clean, invariant.conditions.advance (.BR (.mk_uN depth)), known,
    .terminal dead entered (retained.branch_forward frame index depth scope dst src count old site fixups found framePosition
      scopeAt discarded stackEq destination source width sitePosition appended codeEq framesEq localsEq),
    invariant.arms.branch_forward retained.sites frame index depth dst src count old site fixups found framePosition sitePosition appended codeEq framesEq,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) maps)
      (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩

theorem CompilerPrefix.branch_if_forward {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition stack}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (stable : CompilerStable before after) (maps : after.function.controls = before.function.controls)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame) (forward : frame.kind ≠ .Loop)
    (framePosition : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (inputStack : Sequence.stackTypes raw = stack ++ [.I32])
    (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length + (if count = 0#u32 ∨ src = dst then 0 else 2))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count old condition resume)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (sourceTypes : SourceStack nextRaw stack) (layout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack)
    (resumePosition : resume.val = before.function.code.val.length + (if count = 0#u32 ∨ src = dst then 1 else 3)) (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact retained.localsEq
  have frames := (invariant.frames.record_branch index frame fixups found forward framesEq
    (fun _ _ shape => shape.extend (branchIfInstructions dst src count old condition resume) codeEq (by rw [maps]))).advance (.BR_IF (.mk_uN depth))
  have clean : DormantFrames after.frames.val := by
    rw [framesEq]
    exact invariant.frames.record_branch_dormant invariant.entryChain entered invariant.dormant index frame fixups found
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]
    unfold branchIfInstructions
    split <;> simp
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.advance (.BR_IF (.mk_uN depth)), clean, invariant.conditions.advance (.BR_IF (.mk_uN depth)), sourceTypes.concrete,
    .live live entered ?_,
    invariant.arms.branch_if_forward retained.sites frame index depth dst src count old condition resume site fixups found framePosition sitePosition appended codeEq framesEq,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport (congrArg (fun maps => maps.val.length) maps)
      (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  have next := (inputStack ▸ retained).branch_if_forward frame index depth scope dst src count old condition resume site fixups
    found framePosition scopeAt discarded stackEq destination source width sitePosition appended codeEq framesEq localsEq
    layout conditionSlot resumePosition
  simpa only [sourceTypes.decoded] using next

end Exec.Code
