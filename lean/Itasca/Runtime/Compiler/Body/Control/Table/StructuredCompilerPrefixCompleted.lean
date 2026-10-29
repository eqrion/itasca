import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCompletedPrefix
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- An entered source arm ends either with its exact result stack or with the
retained terminal source prefix. The actual compiler bit selects its exit kind. -/
theorem StructuredCompilerPrefix.completed {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results) :
    StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current before.reachable := by
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

end Itasca.Runtime.Code
