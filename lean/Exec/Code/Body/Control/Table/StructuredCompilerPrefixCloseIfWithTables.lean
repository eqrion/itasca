import Exec.Code.Body.Control.Table.StructuredCompilerPrefixCloseBlockWithTables
import Exec.Code.Local.Control.Table.StructuredUniversalCloseIfWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A live-entered IF without ELSE restores the identity arm at END, so the
parent becomes live even when the then body itself ended in a branch. -/
theorem StructuredCompilerPrefixWithTables.close_if {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype) (guard : Usize) (condition old : U32)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (guardEq : frame.if_pc = some guard)
    (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target)
    (form : child.form = .then_ bt condition)
    (signature : BlockSignature types bt child.params child.results)
    (sameTypes : child.params = child.results) (live : after.reachable = true)
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE bt child.source [])) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have entry : child.entry = guard.val := by
    simpa [guardEq, SourceScope.guardPosition, form, entered] using shape.guard.symm
  have body : child.bodyPc = child.entry + 1 := by
    simpa [SourceScope.bodyStart, form, entered] using shape.body
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  have distinct := invariant.frames.distinct_guard after.frames.val frame framesEq guard guardEq
  have conditionSlot : condition.val = slots locals + slots child.input := by
    have stored : child.entered = true → condition.val = slots locals + slots child.input := by
      simpa [ScopeCondition, form] using invariant.conditions.current
    exact stored entered
  obtain ⟨next, arms⟩ := (invariant.completed entered stack).close_if invariant.arms frame target bt
    guard condition old framesEq kind guardEq guardCode distinct (shape.height entered) shape.results positionEq codeEq
    localsEq layout form entry body conditionSlot sameTypes parentEntered entered signature
  have frames := (invariant.frames.close_guard frame guard condition old target framesEq guardEq guardCode
    branches codeEq (by rw [maps])).advance (.IFELSE bt child.source [])
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patchCode_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  refine StructuredPrefixModeWithTables.live live (by exact parentEntered) ?_
  simpa only [sourceTypes.decoded] using next
end Exec.Code
