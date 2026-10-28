import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefixCompleted
import Itasca.Runtime.Code.Body.Control.Table.StructuredPrefixDead
import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalCloseDeadBlock
import Itasca.Runtime.Code.Local.Control.Table.StructuredElseFrames
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeStackClose
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Closing an entered BLOCK restores either its live parent prefix or its
terminal parent prefix, according to the actual normal/branch exit flags. -/
theorem StructuredCompilerPrefix.close_block {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (form : child.form = .block bt)
    (signature : BlockSignature types bt child.params child.results)
    (exit : after.reachable = (before.reachable || frame.end_reachable))
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.BLOCK bt child.source)) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Block := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    simpa [form, SourceScope.guardPosition] using guard
  have entry : child.entry = child.bodyPc := by
    simpa [form, SourceScope.bodyStart] using shape.body.symm
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have height := shape.height entered
  have width := shape.results
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], before.reachable, frame.end_reachable⟩
  have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
    refine ⟨fun _ => height, fun _ => width, ?_, Nat.le_of_eq positionEq.symm,
      fun _ => Nat.le_of_eq positionEq.symm, ?_, ?_, fun h => h, ?_, ?_⟩
    · intro _; simpa [kind, label] using width
    · simp [kind]
    · simp [kind]
    · intros; rfl
    · simp [noGuard]
  have labelShape : ScopeLabel child label := by
    refine ⟨rfl, ?_, rfl⟩
    simp [SourceScope.branchTypes, form, label]
  have arms := invariant.arms.pop frame label 0#u32 framesEq future labelShape
    (by simpa [frameGroups, noGuard, label, resolvedCode] using codeEq) (.BLOCK bt child.source)
  have frames := (invariant.frames.close_branches frame target framesEq branches codeEq (by rw [maps])).advance (.BLOCK bt child.source)
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patchCode_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, (fun _ => sourceTypes.concrete), ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
  cases mode : invariant.mode with
  | live reachable childEntered retained =>
    have typed := stack reachable
    have next := (typed ▸ retained).close_block frame target bt framesEq kind noGuard height width
      positionEq codeEq localsEq layout form entry parentEntered entered signature
    refine StructuredPrefixMode.live (current := parent.advance (.BLOCK bt child.source)) (by simp [exit, reachable]) (by exact parentEntered) ?_
    simpa only [sourceTypes.decoded] using next
  | terminal dead childEntered retained =>
    cases branchesLive : frame.end_reachable with
    | false =>
      exact .terminal (by simp [exit, dead, branchesLive]) parentEntered
        (retained.close_block_dead frame target bt framesEq kind noGuard height width positionEq codeEq localsEq
          branchesLive form entry parentEntered entered signature)
    | true =>
      refine StructuredPrefixMode.live (current := parent.advance (.BLOCK bt child.source)) (by simp [exit, dead, branchesLive]) (by exact parentEntered) ?_
      have next := retained.close_block_resume frame target bt framesEq kind noGuard height width positionEq codeEq
        localsEq layout branchesLive form entry parentEntered entered signature
      simpa only [sourceTypes.decoded] using next
  | dormant dead retained =>
    have impossible := retained.unentered
    simp [entered] at impossible
end Itasca.Runtime.Code
