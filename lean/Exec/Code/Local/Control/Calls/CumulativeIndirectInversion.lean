import Exec.Code.Local.Relations.Calls.IndirectCallExclusions
import Exec.Code.Local.Relations.Calls.IndirectCallInversion
namespace Exec.Code

theorem CumulativeEmission.indirect_inv {pairs C before emitted after table type}
    (head : CumulativeEmission pairs C before (.CALL_INDIRECT table type) emitted after) :
    IndirectCallEmission pairs C before (.CALL_INDIRECT table type) emitted after := by
  cases head with
  | left h => exact False.elim (float_emission_not_indirect h)
  | right h => exact False.elim (stateful_emission_not_indirect h)
  | indirect h => exact h
end Exec.Code
