import Exec.Code.Local.Relations.Table.BranchTableFrames
import Exec.Code.Local.Relations.Table.BranchTableArguments

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Independent branch widths for the retained table labels. Only labels
actually named by the table must have operands in the current stack. -/
def TableWidthsFit {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ depth ∈ compiler.table_depths.val, ∀ (index : Usize) (frame : runtime.compiler.Frame),
    compiler.frames.val[index.val]? = some frame →
    index.val + depth.val + 1 = compiler.frames.val.length →
    (frameBranchWidth frame).val + 1 ≤ compiler.height.val

/-- Forward relocations change no source label's argument width. -/
theorem TableTargetCode.widths {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depth} (effect : TableTargetCode before after depth) :
    after.frames.val.map frameBranchWidth = before.frames.val.map frameBranchWidth := by
  cases effect with
  | loop _ _ _ _ _ _ _ _ frames => rw [frames]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames,List.map_set]
    have selected : (before.frames.val.map frameBranchWidth)[index.val]? = some (frameBranchWidth frame) := by
      simp only [List.getElem?_map,lookup,Option.map_some]
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    have same := (List.getElem?_eq_some_iff.mp selected).2
    change (before.frames.val.map frameBranchWidth).set index.val (frameBranchWidth frame) = _
    rw [← same]
    exact List.set_getElem_self bound

/-- The source operand condition survives every checked table stub, including
updates to a label subsequently targeted again by another arm. -/
theorem TableWidthsFit.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {chosen} (fits : TableWidthsFit before) (effect : TableTargetCode before after chosen)
    (depths : after.table_depths = before.table_depths) (height : after.height = before.height) :
    TableWidthsFit after := by
  intro depth member index frame lookup position
  have frameBound := (List.getElem?_eq_some_iff.mp lookup).1
  have oldBound : index.val < before.frames.val.length := by rw [effect.frame_length] at frameBound; exact frameBound
  let old := before.frames.val[index.val]
  have oldLookup : before.frames.val[index.val]? = some old := List.getElem?_eq_getElem oldBound
  have widths := congrArg (fun values => values[index.val]?) effect.widths
  simp only [List.getElem?_map,lookup,oldLookup,Option.map_some,Option.some.injEq] at widths
  have memberBefore : depth ∈ before.table_depths.val := by simpa only [depths] using member
  have beforePosition : index.val + depth.val + 1 = before.frames.val.length := by
    rw [effect.frame_length] at position
    exact position
  rw [height,widths]
  exact fits depth memberBefore index old oldLookup beforePosition

end Exec.Code
