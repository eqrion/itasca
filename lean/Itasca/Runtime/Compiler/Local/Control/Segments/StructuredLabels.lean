import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition

/-!
Extending an aligned structured label sequence.

Main declarations: `ExitAligned.cons`. A direct consumer is `Compiler.Local.Control.Table.StructuredCodeLabels`.
-/

namespace Itasca.Runtime.Code
open Aeneas.Std

theorem ExitAligned.cons (label : LabelTarget) (labels : List LabelTarget) :
    ExitAligned (label :: labels) label.normalExit := by
  intro found lookup
  have same : found = label := by simpa using lookup.symm
  subst found
  rfl

end Itasca.Runtime.Code
