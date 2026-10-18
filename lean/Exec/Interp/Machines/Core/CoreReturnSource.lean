import Exec.Interp.Calls.ReturnRefinement
import Exec.Abs.Core

namespace Exec.Interp

/-- Return changes caller values but never caller syntax; the source slice is
therefore preserved for both a resumed caller and a final result. -/
theorem returnedState_core {s : store} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (slice : Abs.CoreState ⟨s, ambient, f :: rest, []⟩) (results : List val) :
    Abs.CoreState (returnedState s ambient rest results) := by
  cases rest with
  | nil => exact ⟨by simp [returnedState, Forall], slice.functions⟩
  | cons caller rest =>
    refine ⟨?_, slice.functions⟩
    intro frame member
    change frame ∈ { caller with vals := caller.vals ++ results } :: rest at member
    rcases List.mem_cons.mp member with rfl | member
    · exact slice.active caller (by simp)
    · exact slice.active frame (by simp [member])

end Exec.Interp
