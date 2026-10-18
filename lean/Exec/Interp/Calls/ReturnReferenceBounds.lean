import Exec.Interp.Calls.ReturnResult
import Exec.Abs.ReferenceBounds

namespace Exec.Interp

theorem returnedState_referenceBound {bound : Nat} {s : store} {ambient : frame}
    {f : Abs.AFrame} {rest : List Abs.AFrame} {results : List val}
    (bounded : Abs.StateReferencesBound bound ⟨s, ambient, f :: rest, []⟩)
    (values : Abs.ValuesBound bound results) :
    Abs.StateReferencesBound bound (returnedState s ambient rest results) := by
  cases rest with
  | nil => exact ⟨values, by simp [returnedState]⟩
  | cons caller rest =>
    refine ⟨Abs.valuesBound_nil _, ?_⟩
    intro item member
    simp only [returnedState, List.mem_cons] at member
    rcases member with rfl | member
    · have saved := bounded.2 caller (by simp)
      exact ⟨saved.1, Abs.valuesBound_append.mpr ⟨saved.2, values⟩⟩
    · exact bounded.2 item (by simp [member])

end Exec.Interp
