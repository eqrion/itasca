import Exec.Interp.Relations.Readback
import Exec.Abs.Results

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem resultIndexFits_of_nonreference (value : val)
    (function : Code.valueType value ≠ .FUNCREF)
    (external : Code.valueType value ≠ .EXTERNREF) : ResultIndexFits value := by
  cases value <;> simp_all [ResultIndexFits, Code.valueType]

/-- Non-reference signatures need no additional issued-address premise for
result decoding. Reference signatures retain that provenance obligation. -/
theorem results_fit_of_types (values : List val) (types : List valtype)
    (typed : values.map Code.valueType = types)
    (nonreference : ∀ ty ∈ types, ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF) :
    ∀ value ∈ values, ResultIndexFits value := by
  intro value member
  have memberType : Code.valueType value ∈ types := by
    rw [← typed]
    exact List.mem_map.mpr ⟨value, member, rfl⟩
  exact resultIndexFits_of_nonreference value (nonreference _ memberType).1 (nonreference _ memberType).2

end Exec.Interp
