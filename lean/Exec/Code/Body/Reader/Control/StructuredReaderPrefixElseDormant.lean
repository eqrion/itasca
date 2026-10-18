import Exec.Code.Body.Control.Control.StructuredCompilerPrefixElseDormant
import Exec.Code.Local.Callbacks.Control.EnterElse
import Exec.Code.Local.Callbacks.Common.CompilerCloseMetadata
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Relations.Control.ControlSources
import Exec.Code.Local.Relations.Control.ControlMapCounts
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- An actual ELSE in an omitted IF changes only its retained source arm and
physical frame kind. No emitted-code relation is assumed for the omitted arm. -/
theorem structured_callback_else_dormant_prefix {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (unentered : current.entered = false)
    (state : code.OpIterState) (bt : signature.BlockType)
    (sourceType : blocktype) (condition : U32) (form : current.form = .then_ sourceType condition)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ∃ noEntry : U32, noEntry.val = before.function.code.val.length ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents
        (current.begin_else sourceType condition noEntry.val noEntry false) state.vals.val state.pos.val := by
  have dead : before.reachable = false := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal dead _ _ => exact dead
    | dormant dead _ => exact dead
  obtain ⟨prior, frame, framesEq, _, shape⟩ := invariant.frames.split
  have noGuard : frame.if_pc = none := by
    simpa [SourceScope.guardPosition, form, unentered] using shape.guard
  have effect := compiler_else_unentered ops law before state bt frame prior framesEq dead noGuard
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨reach, codeEq, afterFrames⟩ := effect rfl
  dsimp only at reach codeEq afterFrames
  have deadAfter : after.reachable = false := reach.trans (shape.entered.trans unentered)
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let noEntry : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : noEntry.val = before.function.code.val.length := rfl
  have stable := compiler_else_stable_result ops law before after state bt (.Ok ()) accepted
  have maps := compiler_else_map_count ops law before after state bt (.Ok ()) accepted
  have sources := compiler_else_sources ops law before after state bt accepted
  have cursor := compiler_else_cursor ops law before after state bt accepted
  exact ⟨noEntry, positionEq, invariant.begin_else_dormant unentered deadAfter stable maps prior frame
    framesEq afterFrames codeEq sourceType condition noEntry form positionEq  sources consumed (by rw [cursor])⟩
end Exec.Code
