import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.Interp.Calls.ReturnRefinement

/-!
Returning retains only the existing result suffix and the saved callers; no returned reference can acquire a different owner.

Main declarations: `returnedState_owned`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp
open Abs.Ownership

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
end Itasca.Runtime.Interp
