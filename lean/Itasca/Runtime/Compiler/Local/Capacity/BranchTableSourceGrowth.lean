import Itasca.Runtime.Compiler.Local.Capacity.BranchTableGrowth
import Itasca.Binary.Wasm1.BrTableLabels
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Each accepted label consumes at least one source byte, including nonminimal
LEB encodings. -/
theorem table_labels_byte_bound {data start depths next}
    (decoded : BrTable.LabelsDecoded data start depths next) :
    start.val+depths.length≤next.val := by
  induction decoded with
  | nil => simp
  | snoc prior label ih =>
    have consumed := label.span
    simp only [List.length_append,List.length_singleton]
    omega

theorem table_immediate_byte_bound {data start depths fallback next}
    (decoded : BrTable.Decoded data start depths fallback next) :
    start.val+depths.length+2≤next.val := by
  obtain ⟨count,first,last,countDecoded,_,labels,defaultDecoded⟩ := decoded
  have countBytes := countDecoded.span
  have labelsBytes := table_labels_byte_bound labels
  have defaultBytes := defaultDecoded.span
  omega

end Itasca.Runtime.Code
