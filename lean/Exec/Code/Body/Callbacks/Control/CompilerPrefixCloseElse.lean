import Exec.Code.Body.Callbacks.Common.CompilerPrefixCompleted
import Exec.Code.Body.Callbacks.Common.CompilerPrefixDead
import Exec.Code.Local.Control.Control.UniversalCloseDeadElse
import Exec.Code.Local.Control.Control.UniversalCloseElse
import Exec.Code.Local.Callbacks.Control.ElseFrames
import Exec.Code.Local.Callbacks.Control.ScopeStackClose
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Closing an explicit ELSE joins the saved then arm and completed else
arm, preserving either a live or a terminal parent continuation. -/
theorem CompilerPrefix.close_else {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents parent child raw position nextRaw nextPosition}
    (invariant : CompilerPrefix initial before types functions returns locals (parents ++ [parent]) child raw position)
    (entered : child.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = child.front ++ child.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (framesEq : before.frames.val = after.frames.val ++ [frame])
    (positionEq : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (form : child.form = .else_ bt condition yes yesExit noEntry yesNormal)
    (signature : BlockSignature types bt child.params child.results)
    (exit : after.reachable = (before.reachable || frame.end_reachable))
    (layout : CompilerLayout after (child.front ++ child.results))
    (sourceTypes : SourceStack nextRaw (child.front ++ child.results))
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts after.frames.val frame framesEq
  have kind : frame.kind = .Else := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    have guard := shape.guard
    simpa [form, SourceScope.guardPosition] using guard
  have parentEntered := invariant.entryChain.ancestor entered parent (by simp)
  have height := shape.height entered
  have width := shape.results
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have branches := (invariant.mode.sites frame (by simp [framesEq])).branches
  have yesClosed := shape.elseLive bt condition yes yesExit noEntry yesNormal form
  have completed := invariant.completed entered stack
  have result : PrefixMode after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) (Sequence.stackTypes nextRaw) ∧
      UniversalElse after types functions returns locals parents (parent.advance (.IFELSE bt yes child.source)) := by
    cases normal : before.reachable with
    | true =>
      obtain ⟨next, arms⟩ := completed.close_else invariant.arms frame target bt condition noEntry yes yesExit yesNormal
        framesEq kind noGuard height width positionEq codeEq localsEq layout form parentEntered entered signature
      refine ⟨PrefixMode.live (current := parent.advance (.IFELSE bt yes child.source)) (by simp [exit, normal]) (by exact parentEntered) ?_, arms⟩
      simpa only [sourceTypes.decoded] using next
    | false =>
      cases marked : frame.end_reachable with
      | true =>
        obtain ⟨next, arms⟩ := completed.close_else invariant.arms frame target bt condition noEntry yes yesExit yesNormal
          framesEq kind noGuard height width positionEq codeEq localsEq layout form parentEntered entered signature
        refine ⟨PrefixMode.live (current := parent.advance (.IFELSE bt yes child.source)) (by simp [exit, normal, marked]) (by exact parentEntered) ?_, arms⟩
        simpa only [sourceTypes.decoded] using next
      | false =>
        have yesDead : yesNormal = false := by
          cases yesEq : yesNormal with
          | false => rfl
          | true => have impossible := yesClosed yesEq; simp [marked] at impossible
        obtain ⟨next, arms⟩ := (normal ▸ completed).close_else_dead invariant.arms frame target bt condition noEntry yes yesExit yesNormal
          framesEq kind noGuard height width positionEq codeEq localsEq marked yesDead form parentEntered entered signature
        exact ⟨PrefixMode.terminal (current := parent.advance (.IFELSE bt yes child.source)) (by simp [exit, normal, marked]) (by exact parentEntered) next, arms⟩
  have frames := (invariant.frames.close_branches frame target framesEq branches codeEq (by rw [maps])).advance (.IFELSE bt yes child.source)
  have clean : DormantFrames after.frames.val := (framesEq ▸ invariant.dormant).pop
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by simp [codeEq, patchCode_length]
  refine ⟨invariant.metadata.trans stable, frames, invariant.entryChain.pop.advance _, clean,
    invariant.conditions.pop.advance _, sourceTypes.concrete, result.1, result.2, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by omega) consumed,
    (invariant.controlBudget.transport maps (by simp [framesEq])).advance (Nat.le_of_lt consumed), cursor⟩
end Exec.Code
