import Exec.Code.Body.Control.Table.StructuredCompilerPrefixEndEffects
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixCloseDormant
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Relations.Control.ControlSources
import Exec.Code.Local.Relations.Control.ControlMapCounts
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_callback_end_dormant_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (unentered : current.entered = false) (nonBody : current.form.kind ≠ .Body)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) (instruction : instr)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    after.reachable = false ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
        (parent.advance instruction) state.vals.val state.pos.val := by
  have dead : before.reachable = false := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal dead _ _ => exact dead
    | dormant dead _ => exact dead
  have noGuard : current.guardPosition = none := by
    cases form : current.form <;> simp [SourceScope.guardPosition, form, unentered]
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, patched⟩ := invariant.end_unguarded ops law
    nonBody noGuard state kind bt coordinate sourceBound accepted
  have frameDead := shape.entered.trans unentered
  obtain ⟨noExit, noFixups⟩ := invariant.dormant frame (by simp [framesEq]) frameDead
  have deadAfter : after.reachable = false := by
    cases kindEq : frame.kind <;> simpa [scopeExitLive, dead, noExit, frameDead, kindEq] using reachable
  have codeEq : after.function.code.val = before.function.code.val := by
    simpa [noFixups, patchCode] using patched
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  exact ⟨deadAfter, invariant.close_dormant unentered deadAfter stable maps frame target instruction framesEq
    targetAt codeEq  sources consumed (by rw [cursor])⟩
end Exec.Code
