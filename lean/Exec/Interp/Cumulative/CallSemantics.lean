import Exec.Interp.StructuredMachine.CallSemantics
import Exec.Abs.Cumulative.PureCoverage
import Exec.Abs.Stateful.OwnershipStore
namespace Exec.Interp.Cumulative

def callSemantics : StructuredMachine.CallSemantics Abs.CumulativeState Abs.Ownership.StatefulOwned where
  covered s ambient f rest index after frames covered step :=
    Abs.Cumulative.slice_instruction_covered s ambient f rest (.CALL (.mk_uN index)) after _ (.call _) covered step
  ownership := by
    intro s ambient f rest index after frames step bounds owned
    exact ⟨Abs.Ownership.instruction_ownership bounds s ambient f rest (.CALL (.mk_uN index)) after _ [] (.call _)
      (owned.values.2 {f with code := .CALL (.mk_uN index)::after} (by simp))
      (fun frame member => owned.values.2 frame (by simp [member])) owned.values.1 step,owned.heap⟩
end Exec.Interp.Cumulative
