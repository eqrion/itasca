import Itasca.Support.Result
import Itasca.Visitor.Refinement
import Itasca.Handler.BrTable

/-!
# Refinement of the `br_table` reader

Lifts a `VisitorTrace.Refines` relation between visitors to the label loop
`code.read_table_labels_loop`, the label reader `code.read_table_labels` and the full
`code.read_br_table`, so results and validator state agree on every normal return.
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace

end Itasca
