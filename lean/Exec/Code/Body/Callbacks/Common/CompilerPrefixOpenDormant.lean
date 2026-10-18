import Exec.Code.Body.Callbacks.Common.CompilerPrefixDead
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Callbacks.Control.ElseFrames
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Opening source inside a terminal or omitted prefix retains only the saved
parent code. No executable relation is asserted for the new omitted child. -/
theorem CompilerPrefix.open_dormant {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (dead : before.reachable = false) (deadAfter : after.reachable = false)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (stable : CompilerStable before after)
    (aligned : ScopeFrameStack locals after (parents ++ [current]) child)
    (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (clean : DormantFrame frame) (fresh : child.form.isElse = false)
    (known : ConcreteStack nextRaw) (childEntered : child.entered = false)
    (entry : child.entry = before.function.code.val.length)
    (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    CompilerPrefix initial after types functions returns locals (parents ++ [current]) child nextRaw nextPosition := by
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]
    exact invariant.mode.locals
  have childCondition : ScopeCondition locals child := by
    unfold ScopeCondition
    split <;> simp [childEntered]
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by rw [codeEq]; omega
  refine ⟨invariant.metadata.trans stable, aligned,
    invariant.entryChain.push child (by simp [childEntered]),
    (by rw [framesEq]; exact invariant.dormant.push frame clean),
    invariant.conditions.push child childCondition, known, ?_,
    invariant.arms.open_plain invariant.mode.sites child frame [] fresh
      (by simp [codeEq]) framesEq noGuard noBranches,
    sources.aligned invariant.sources, invariant.codeBudget.advance growth consumed,
    invariant.controlBudget.enter maps (by simp [framesEq]) consumed, cursor⟩
  apply PrefixMode.dormant deadAfter
  cases invariant.mode with
  | live reachable _ _ => simp [dead] at reachable
  | terminal _ parentEntered retained =>
    exact retained.open_dormant child frame codeEq framesEq noGuard noBranches localsEq parentEntered childEntered entry
  | dormant _ retained =>
    exact retained.open_dormant child frame codeEq framesEq noGuard noBranches localsEq childEntered entry

end Exec.Code
