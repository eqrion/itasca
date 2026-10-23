import Exec.Code.Local.Control.Common.StructuredComposition
namespace Exec.Code
open Aeneas.Std

theorem ExitAligned.cons (label : LabelTarget) (labels : List LabelTarget) :
    ExitAligned (label :: labels) label.normalExit := by
  intro found lookup
  have same : found = label := by simpa using lookup.symm
  subst found
  rfl

end Exec.Code
