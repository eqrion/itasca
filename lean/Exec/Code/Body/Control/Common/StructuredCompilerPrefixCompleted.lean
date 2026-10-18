import Exec.Code.Body.Control.Common.StructuredCompilerPrefix
import Exec.Code.Local.Control.Common.StructuredCompletedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- An entered source arm ends either with its exact result stack or with the
retained terminal source prefix. The actual compiler bit selects its exit kind. -/
theorem StructuredCompilerPrefix.completed {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results) :
    StructuredCompletedPrefix emit before types functions returns locals parents current before.reachable := by
  cases invariant.mode with
  | live reachable _ retained =>
    rw [reachable]
    exact (stack reachable ▸ retained).completed
  | terminal dead _ retained =>
    rw [dead]
    exact retained.completed
  | dormant _ retained =>
    have impossible := retained.unentered
    simp [entered] at impossible

end Exec.Code
