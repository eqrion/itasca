import Exec.Code.Body.Control.Table.StructuredCompilerPrefixCompletedWithTables
import Exec.Code.Body.Control.Table.StructuredPrefixDeadWithTables
import Exec.Code.Local.Control.Table.StructuredUniversalCloseLoopWithTables
import Exec.Code.Local.Control.Table.StructuredElseFramesWithTables
import Exec.Code.Local.Callbacks.Control.ScopeStackClose
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Closing an entered LOOP preserves its normal reachability; backward
branches do not create a forward exit. -/
theorem StructuredCompilerPrefixWithTables.close_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (form : child.form = .loop bt)
    (signature : BlockSignature types bt child.params child.results)
    (exit : after.reachable = before.reachable)
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.LOOP bt child.source)) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Loop := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    simpa [form, SourceScope.guardPosition] using guard
  have entry : child.entry = frame.start_pc.val := by
    simpa [form, SourceScope.frameStart] using shape.start.symm
  have body : child.bodyPc = frame.start_pc.val + 1 := by
    simpa [form, SourceScope.bodyStart, entered, entry] using shape.body
  have head : before.function.code.val[frame.start_pc.val]? = some .LoopHead := by
    have actual : before.function.code.val[child.entry]? = some .LoopHead := by
      have hook : child.entered = true → before.function.code.val[child.entry]? = some .LoopHead := by
        simpa [ScopeEntryCode, form] using shape.entryCode
      exact hook entered
    simpa [entry] using actual
  obtain ⟨noFixups, ends⟩ := shape.loopClean bt form
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have height := shape.height entered
  have width := shape.results
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  let label : LabelTarget := ⟨child.front, child.params, child.results, frame.start_pc, target.val, [.LOOP bt child.source], [], before.reachable, true⟩
  have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
    refine ⟨fun _ => height, fun _ => width, ?_, Nat.le_of_eq positionEq.symm, ?_,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
    · intro _; simpa [kind, label] using shape.params
    · simp [kind]
    · simp [kind]
    · simp [noGuard]
  have labelShape : ScopeLabel child label := by
    refine ⟨rfl, ?_, rfl⟩
    simp [SourceScope.branchTypes, form, label]
  have arms := invariant.arms.pop frame label 0#u32 framesEq future labelShape
    (by simpa [frameGroups, noGuard, noFixups, label, resolvedCode, patchCode] using codeEq) (.LOOP bt child.source)
  have frames := (invariant.frames.close_branches frame target framesEq branches (by simpa [noFixups, patchCode] using codeEq) (by rw [maps])).advance (.LOOP bt child.source)
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patchCode_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  cases mode : invariant.mode with
  | live reachable childEntered retained =>
    have typed := stack reachable
    have next := (typed ▸ retained).close_loop frame target bt framesEq kind noGuard noFixups height shape.params width
      positionEq codeEq localsEq layout form entry body head parentEntered entered signature
    refine StructuredPrefixModeWithTables.live (current := parent.advance (.LOOP bt child.source)) (exit.trans reachable) (by exact parentEntered) ?_
    simpa only [sourceTypes.decoded] using next
  | terminal dead childEntered retained =>
    exact .terminal (exit.trans dead) parentEntered
      (retained.close_loop frame target bt framesEq kind noGuard noFixups height shape.params width positionEq codeEq localsEq
        form entry body head parentEntered entered signature)
  | dormant dead retained =>
    have impossible := retained.unentered
    simp [entered] at impossible
end Exec.Code
