import Exec.Code.Local.Callbacks.Control.ScopeFrameSelect
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables
import Exec.Code.Body.Relations.Control.BranchIfLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredCompilerPrefixWithTables.branch_if_coordinates {jumpTables : List Aeneas.Std.U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position stack}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = stack ++ [.I32])
    (targetStack : stack = scope.front ++ discarded ++ scope.branchTypes) :
    ∃ index : Usize, ∃ frame : runtime.compiler.Frame, ∃ source condition : U32,
      before.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = before.frames.val.length ∧
      FrameScope locals before scope frame ∧
      frame.height.val = slots locals + slots scope.front ∧
      source.val = slots locals + slots (scope.front ++ discarded) ∧
      source.val + slots scope.branchTypes + 1 = before.height.val ∧
      before.before.val[before.before.val.length - 1]? = some condition ∧
      condition.val = slots locals + slots stack := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, found, position, shape, _, height⟩ :=
    invariant.frames.selected_live invariant.entryChain entered depth scope selected
  have layout : CompilerLayout before (stack ++ [.I32]) := input ▸ retained.layout
  obtain ⟨condition, conditionAt, conditionSlot⟩ := layout.condition
  have grouped : CompilerLayout before (scope.front ++ discarded ++ (scope.branchTypes ++ [.I32])) := by
    simpa only [targetStack, List.append_assoc] using layout
  obtain ⟨source, sourcePosition, sourceWidth⟩ := branch_source_coordinate grouped retained.localsEq
  refine ⟨index, frame, source, condition, found, position, shape, height, sourcePosition, ?_, conditionAt, ?_⟩
  · simpa [slots_append, slots, width, Nat.add_assoc] using sourceWidth
  · simpa only [retained.localsEq] using conditionSlot

end Exec.Code
