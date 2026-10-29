import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameSelect
import Itasca.Runtime.Compiler.Local.Control.Control.UniversalBranch
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Static source operand suffixes for every independently decoded table arm.
The selector has already been separated from `stack`. -/
def TableOperandScopes (scopes : List SourceScope) (stack : List valtype)
    (depths : List U32) : Prop :=
  ∀ depth ∈ depths, ∃ scope discarded,
    scopes.reverse[depth.val]? = some scope ∧ scope.entered = true ∧
    stack = scope.front ++ discarded ++ scope.branchTypes

private theorem paired_shapes_lookup {locals scopes frames}
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes frames)
    (index : Nat) (scope : SourceScope) (frame : runtime.compiler.Frame)
    (source : scopes[index]? = some scope) (physical : frames[index]? = some frame) :
    ScopeFrameShape locals scope frame := by
  induction paired generalizing index with
  | nil => simp at source
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at source physical
      subst scope frame
      exact head
    | succ index => exact ih index source physical

 theorem table_scope_shape {locals scopes frames}
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes frames)
    (index depth : Nat) (scope : SourceScope) (frame : runtime.compiler.Frame)
    (source : scopes.reverse[depth]? = some scope) (physical : frames[index]? = some frame)
    (position : index+depth+1=frames.length) : ScopeFrameShape locals scope frame := by
  have bound : depth < scopes.length := by
    have bound := (List.getElem?_eq_some_iff.mp source).1
    simpa only [List.length_reverse] using bound
  have lengths := paired.length_eq
  have coordinate : scopes.length-1-depth=index := by omega
  rw [List.getElem?_reverse bound,coordinate] at source
  exact paired_shapes_lookup paired index scope frame source physical

/-- Actual checked subtraction fixes the source slot, while the canonical
source suffix and retained frame shape fix its types and destination. -/
theorem table_operand_layout {locals stack scope label frame discarded}
    (shape : ScopeFrameShape locals scope frame) (typedLabel : ScopeLabel scope label)
    (entered : scope.entered=true)
    (input : stack=scope.front++discarded++scope.branchTypes)
    (source height : U32) (heightEq : height.val=slots locals+slots stack+1)
    (sourceEq : source.val+(frameBranchWidth frame).val+1=height.val) :
    BranchLayout locals stack label frame.height source (frameBranchWidth frame) := by
  have width : (frameBranchWidth frame).val = slots scope.branchTypes := shape.branch_width
  have destination := shape.height entered
  refine ⟨discarded,?_,?_,?_,?_⟩
  · simpa only [typedLabel.front,typedLabel.branchTypes] using input
  · simpa only [typedLabel.front] using destination
  · rw [typedLabel.front]
    rw [input,slots_append,slots_append] at heightEq
    rw [slots_append]
    omega
  · simpa only [typedLabel.branchTypes] using width
end Itasca.Runtime.Compiler
