import Itasca.Runtime.Compiler.Body.Control.Table.StructuredPrefixDead
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixCompleted
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalElse
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeStackElse
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- ELSE retains the completed then arm and restores the sibling's exact
source input, including the original guard coordinate and all outer plans. -/
theorem StructuredCompilerPrefix.begin_else {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (entered : current.entered = true) (live : after.reachable = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (stable : CompilerStable before after)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups before.reachable)
    (bt : blocktype) (form : current.form = .then_ bt condition) (guardEq : frame.if_pc = some guard)
    (layout : CompilerLayout after current.input) (sourceTypes : SourceStack nextRaw current.input)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (current.begin_else bt condition before.function.code.val.length noEntry before.reachable) nextRaw nextPosition := by
  obtain ⟨paired, shape⟩ := invariant.frames.parts prior frame change.beforeFrames
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, stable.fields.2.2.2.2.1]; exact invariant.mode.locals
  have conditionSlot : condition.val = slots locals + slots current.input := by
    have stored := invariant.conditions.current
    have offset : current.entered = true → condition.val = slots locals + slots current.input := by
      simpa only [ScopeCondition, form] using stored
    exact offset entered
  have entry : current.entry = guard.val := by
    have coordinate := shape.guard
    simpa [guardEq, SourceScope.guardPosition, form, entered] using coordinate.symm
  have body : current.bodyPc = current.entry + 1 := by
    simpa [SourceScope.bodyStart, form, entered] using shape.body
  have kind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have distinct := invariant.frames.distinct_guard prior frame change.beforeFrames guard guardEq
  obtain ⟨next, arms⟩ := (invariant.completed entered stack).begin_else invariant.arms prior frame guard site condition old noEntry fixups
    change bt form entered entry body conditionSlot kind guardEq distinct localsEq layout
  have frames := invariant.frames.begin_else prior frame guard site condition old noEntry fixups before.reachable
    change bt form guardEq (by rw [maps])
  have clean : DormantFrames after.frames.val := by
    rw [change.afterFrames]
    have previous : DormantFrames (prior ++ [frame]) := change.beforeFrames ▸ invariant.dormant
    exact previous.replace_last _ (DormantFrame.entered (shape.entered.trans entered))
  have growth : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [change.length, change.noPosition]
    split <;> omega
  refine ⟨invariant.metadata.trans stable, frames,
    invariant.entryChain.begin_else bt condition before.function.code.val.length noEntry before.reachable,
    clean, invariant.conditions.begin_else bt condition form before.function.code.val.length noEntry before.reachable,
    (fun _ => sourceTypes.concrete), .live live entered ?_, arms, sources.aligned invariant.sources,
    invariant.codeBudget.advance growth consumed,
    (invariant.controlBudget.transport maps (by simp [change.afterFrames, change.beforeFrames])).advance (Nat.le_of_lt consumed), cursor⟩
  simpa only [sourceTypes.decoded] using next

end Itasca.Runtime.Compiler
