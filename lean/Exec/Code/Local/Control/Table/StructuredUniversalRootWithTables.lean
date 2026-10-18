import Exec.Code.Local.Control.Table.StructuredUniversalTerminalWithTables
import Exec.Code.Local.Control.Table.StructuredPrefixCloseWithTables
import Exec.Code.Local.Control.Common.UniversalRoot
namespace Exec.Code
open Aeneas.Std
theorem StructuredUniversalPrefixWithTables.root_finish {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current}
    (invariant : StructuredUniversalPrefixWithTables (jumpTables := jumpTables) emit compiler types functions returns locals [] current returns)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    StructuredCodeWithTables emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], true, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target true kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target true frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish (by simp [resolvedCode_length]) (by simp [NormalLive])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

/-- A terminal root body closes at the actual final PC even when its result
signature is nonempty and the emitted unreachable epilogue returns zero words. -/
theorem StructuredUniversalTerminalWithTables.root_finish {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current}
    (invariant : StructuredUniversalTerminalWithTables (jumpTables := jumpTables) emit compiler types functions returns locals [] current)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    StructuredCodeWithTables emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], false, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target false kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target false frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish target.val returns (by omega) (by simp [resolvedCode_length, position])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

end Exec.Code

