import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp
open Aeneas.Std

/-- Appending returned values leaves every saved outer label prefix intact. -/
theorem LabelsMatch.append {values : List val} {labels targets}
    (matching : LabelsMatch values labels targets) (results : List val)
    (heights : ∀ label ∈ labels, label.height ≤ values.length) :
    LabelsMatch (values ++ results) labels targets := by
  apply matching.reprefix
  intro label member
  exact (List.take_append_of_le_length (heights label member)).symm

end Exec.Interp
