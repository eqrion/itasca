import Exec.Abs.Ownership.Core
import Exec.Interp.Calls.ReturnRefinement
namespace Exec.Interp
open Abs.Ownership

/-- Exact abstract steps and source stutters preserve reference provenance.
This uses the executable Core transition, never an arbitrary source trace. -/
theorem core_owned_transition {initial next : Abs.AState}
    (typed : Abs.CoreTyped initial) (covered : Abs.CoreState initial)
    (transition : initial = next ∨ Abs.Core.step initial = .next next) :
    ∀ bounds, CoreOwned bounds initial → CoreOwned bounds next := by
  intro bounds owned
  rcases transition with same | step
  · exact same ▸ owned
  · exact step_owned typed covered owned step

/-- Returning retains only the existing result suffix and the saved callers;
no returned reference can acquire a different owner. -/
theorem returnedState_owned {s : store} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (results : List val) (subset : ∀ value ∈ results, value ∈ f.vals) :
    ∀ bounds, CoreOwned bounds ⟨s,ambient,f::rest,[]⟩ →
      CoreOwned bounds (returnedState s ambient rest results) := by
  intro bounds owned
  have first := owned.values.2 f (by simp)
  have values : ValuesOwned bounds results := fun value member => first.2 value (subset value member)
  cases rest with
  | nil => exact ⟨⟨values,by simp [returnedState]⟩,owned.globals⟩
  | cons caller rest =>
    have saved := owned.values.2 caller (by simp)
    refine ⟨⟨valuesOwned_nil _,?_⟩,owned.globals⟩
    intro item member
    change item ∈ {caller with vals := caller.vals++results}::rest at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨saved.1,valuesOwned_append.mpr ⟨saved.2,values⟩⟩
    · exact owned.values.2 item (by simp [member])
end Exec.Interp
