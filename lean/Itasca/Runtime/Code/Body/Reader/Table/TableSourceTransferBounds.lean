import Itasca.Runtime.Code.Body.Control.Table.StructuredBranchIfLayout
import Itasca.Runtime.Code.Local.Source.TableTransferBounds

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source typing of every table label supplies overlap-safe transfer bounds
and already opened loop targets, including repeated and outer labels. -/
theorem StructuredCompilerPrefix.table_transfer_geometry
    {jumpTables : List U32} {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position stack} {depths : List U32}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current raw position)
    (live : compiler.reachable = true)
    (input : Sequence.stackTypes raw = stack++[.I32])
    (labels : ∀ depth ∈ depths, ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      stack = scope.front++discarded++scope.branchTypes) :
    ∀ depth ∈ depths, ∀ (index : Usize) (frame : runtime.compiler.Frame),
      compiler.frames.val[index.val]? = some frame → index.val+depth.val+1 = compiler.frames.val.length →
      frame.height.val+(frameBranchWidth frame).val+1 ≤ compiler.height.val ∧
        (frame.kind = .Loop → frame.start_pc.val ≤ compiler.function.code.length) := by
  intro depth member index frame found position
  obtain ⟨scope,discarded,selected,targetStack⟩ := labels depth member
  obtain ⟨actual,actualFrame,source,condition,actualFound,actualPosition,shape,height,sourceAt,sourceWidth,_⟩ :=
    invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
  have same : actual = index := UScalar.eq_of_val_eq (by omega)
  subst actual
  rw [found] at actualFound
  cases Option.some.inj actualFound
  have width := shape.toScopeFrameShape.branch_width
  change (frameBranchWidth frame).val = slots scope.branchTypes at width
  have front : slots scope.front ≤ slots (scope.front++discarded) := by
    rw [slots_append]
    omega
  refine ⟨by omega,?_⟩
  intro loop
  have kind := shape.kind
  have start := shape.start
  have entry := shape.entryBound
  cases form : scope.form <;> simp_all [ScopeForm.kind,SourceScope.frameStart]

end Itasca.Runtime.Code
