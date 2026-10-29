import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameSelect
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchEffects
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout

/-!
Exact live branch slot coordinates follow from source scope selection and the compiler's current layout; no equality of word widths substitutes for a target's source type list.

Main declarations: `StructuredCompilerPrefix.branch_layout`. A direct consumer is `Compiler.Body.Reader.Control.ReachedBranchAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Exact live branch slot coordinates follow from source scope selection and
the compiler's current layout; no equality of word widths substitutes for a
target's source type list. -/
theorem StructuredCompilerPrefix.branch_layout {jumpTables : List Aeneas.Std.U32} {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes) :
    ∃ index : Usize, ∃ frame : runtime.compiler.Frame, ∃ source : U32,
      before.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = before.frames.val.length ∧
      FrameScope locals before scope frame ∧
      frame.height.val = slots locals + slots scope.front ∧
      source.val = slots locals + slots (scope.front ++ discarded) ∧
      source.val + slots scope.branchTypes = before.height.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, found, position, shape, _, height⟩ :=
    invariant.frames.selected_live invariant.entryChain entered depth scope selected
  obtain ⟨source, sourcePosition, sourceWidth⟩ := branch_source_coordinate
    (input ▸ retained.layout) retained.localsEq
  exact ⟨index, frame, source, found, position, shape, height, sourcePosition, sourceWidth⟩

end Itasca.Runtime.Code
