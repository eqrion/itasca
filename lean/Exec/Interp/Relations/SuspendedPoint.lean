import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp
open Aeneas.Std

/-- A suspended caller retains the code certificate for its continuation with
its callee's result types appended. Those values do not yet occupy live slots. -/
structure SuspendedFramePoint (raw : runtime.interp.Frame) (source : Abs.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output waiting : List valtype) : Prop where
  labels : LabelsMatch source.vals source.labels targets
  code : Code.StructuredPoint source.module.TYPES functions source.resultTypes
    (source.locals.map Code.valueType) compiled.code.val targets
    (source.vals.map Code.valueType ++ waiting) source.code raw.pc.val next output

/-- Appending returned values leaves every saved outer label prefix intact. -/
theorem LabelsMatch.append {values : List val} {labels targets}
    (matching : LabelsMatch values labels targets) (results : List val)
    (heights : ∀ label ∈ labels, label.height ≤ values.length) :
    LabelsMatch (values ++ results) labels targets := by
  apply matching.reprefix
  intro label member
  exact (List.take_append_of_le_length (heights label member)).symm

/-- Checked returned values activate exactly the previously retained caller
continuation, including every still-live branch target. -/
theorem SuspendedFramePoint.resume {raw source compiled functions targets next output waiting}
    (point : SuspendedFramePoint raw source compiled functions targets next output waiting)
    (results : List val) (types : results.map Code.valueType = waiting)
    (heights : Abs.FrameHeights source) :
    StructuredFramePoint raw { source with vals := source.vals ++ results }
      compiled functions targets next output := by
  refine ⟨point.labels.append results heights, ?_⟩
  simpa only [List.map_append, types] using point.code

/-- The CALL continuation becomes a suspended point after removing argument
values. The source call preservation theorem supplies saved-label height bounds. -/
theorem StructuredFramePoint.suspend {raw source compiled functions targets next output}
    (point : StructuredFramePoint raw source compiled functions targets next output)
    (front args : List val) (after : List instr) (pc : Aeneas.Std.U32) (returns : List valtype)
    (split : source.vals = front ++ args)
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Code.CodeRel source.module.TYPES functions source.resultTypes
      (source.locals.map Code.valueType) compiled.code.val targets
      (front.map Code.valueType ++ returns) after pc.val next output) :
    SuspendedFramePoint { raw with pc := pc } { source with vals := front, code := after }
      compiled functions targets next output returns := by
  refine ⟨?_, ⟨continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩⟩
  apply point.labels.reprefix
  intro label member
  rw [split, List.take_append_of_le_length (heights label member)]

end Exec.Interp
