import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixElse
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalDormantElse
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeStackClose
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An ELSE reached inside an unentered IF changes the retained source arm
without assigning bytecode to either omitted arm. -/
theorem StructuredCompilerPrefix.begin_else_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (unentered : current.entered = false) (dead : after.reachable = false)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (beforeFrames : before.frames.val = prior ++ [frame])
    (afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}])
    (codeEq : after.function.code = before.function.code)
    (bt : blocktype) (condition noEntry : U32) (form : current.form = .then_ bt condition)
    (positionEq : noEntry.val = before.function.code.val.length)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (current.begin_else bt condition noEntry.val noEntry false) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts prior frame beforeFrames
  have kind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have noGuard : frame.if_pc = none := by
    simpa [SourceScope.guardPosition, form, unentered] using shape.guard
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have retained : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals parents current := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal _ entered _ => simp [unentered] at entered
    | dormant _ retained => exact retained
  obtain ⟨next, arms⟩ := retained.begin_else invariant.arms prior frame beforeFrames afterFrames kind noGuard
    codeEq localsEq bt condition noEntry noEntry.val false form
  have frames := invariant.frames.begin_else_dormant prior frame bt condition form noEntry positionEq
    beforeFrames afterFrames (congrArg (fun code => code.val) codeEq) (by rw [maps])
  have clean : DormantFrames after.frames.val := by
    rw [afterFrames]
    have previous : DormantFrames (prior ++ [frame]) := beforeFrames ▸ invariant.dormant
    apply previous.replace_last
    intro inactive
    exact previous frame (by simp) inactive
  refine ⟨invariant.metadata.trans stable, frames,
    invariant.entryChain.begin_else bt condition noEntry.val noEntry false, clean,
    invariant.conditions.begin_else bt condition form noEntry.val noEntry false, (by intro live; simp [dead] at live),
    .dormant dead next, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance (by simp [codeEq]) consumed,
    (invariant.controlBudget.transport maps (by simp [beforeFrames, afterFrames])).advance (Nat.le_of_lt consumed), cursor⟩
end Itasca.Runtime.Compiler
