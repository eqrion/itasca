import Exec.Spec.Choices.NumericChoices
import Exec.Spec.Choices.VectorChoices

/-! Source policies can realize any independently admissible scalar or SIMD
reply at a specified occurrence. These existence results do not claim that a
concrete interpreter selects that policy or that ordinary steps are deterministic. -/

namespace Exec.Spec

/-- Replace one independently specified request/occurrence in a source policy. -/
noncomputable def sourcePolicyOverride {Request Reply : Type} (base : Nat → Request → Reply)
    (occurrence : Nat) (request : Request) (reply : Reply) : Nat → Request → Reply := by
  classical
  exact fun n key => if n = occurrence ∧ key = request then reply else base n key

theorem sourcePolicyOverride_selected {Request Reply : Type} (base : Nat → Request → Reply)
    (occurrence : Nat) (request : Request) (reply : Reply) :
    sourcePolicyOverride base occurrence request reply occurrence request = reply := by
  classical
  simp [sourcePolicyOverride]

theorem sourcePolicyOverride_preserves {Request Reply : Type} (permitted : Request → Reply → Prop)
    (base : Nat → Request → Reply) (allowed : ∀ n key, permitted key (base n key))
    (occurrence : Nat) (request : Request) (reply : Reply) (selected : permitted request reply) :
    ∀ n key, permitted key (sourcePolicyOverride base occurrence request reply n key) := by
  classical
  intro n key
  unfold sourcePolicyOverride
  split
  · rename_i same
    rcases same with ⟨rfl,rfl⟩
    exact selected
  · exact allowed n key

def NumericReplyAllowed (results : List num_) (reply : Option num_) : Prop :=
  (reply = none ↔ results = []) ∧ ∀ value, reply = some value → value ∈ results

/-- Every source-permitted scalar reply is selectable by an admissible policy.
No concrete interpreter result occurs in these premises. -/
theorem numeric_reply_selectable (occurrence : Nat) (request : NumericRequest)
    (results : List num_) (source : request.Allowed results) (reply : Option num_)
    (permitted : NumericReplyAllowed results reply) :
    ∃ choices : NumericChoices, choices.Admissible ∧ ChosenNumeric choices occurrence request reply := by
  let allowed (key : NumericRequest × List num_) (answer : Option num_) : Prop :=
    key.1.Allowed key.2 → NumericReplyAllowed key.2 answer
  let base : Nat → NumericRequest × List num_ → Option num_ := fun n key => firstNumericChoice n key.1 key.2
  let selected := sourcePolicyOverride base occurrence (request,results) reply
  let choices : NumericChoices := fun n key values => selected n (key,values)
  have admissible : ∀ n key, allowed key (selected n key) :=
    sourcePolicyOverride_preserves allowed base (fun n key => firstNumericChoice_admissible n key.1 key.2)
      occurrence (request,results) reply (fun _ => permitted)
  refine ⟨choices,?_,?_⟩
  · intro n key values typed
    exact admissible n (key,values) typed
  · have chosen : choices occurrence request results = reply := sourcePolicyOverride_selected base occurrence (request,results) reply
    rw [←chosen]
    exact .selected results source

theorem vector_reply_selectable (occurrence : Nat) (request : VectorRequest) (reply : Option vec_)
    (permitted : VectorResultAllowed request reply) :
    ∃ choices : VectorChoices, choices.Admissible ∧ ChosenVector choices occurrence request reply := by
  let choices := sourcePolicyOverride sourceVectorChoice occurrence request reply
  have allowed : ∀ n key, (∃ value, VectorResultAllowed key value) → VectorResultAllowed key (choices n key) :=
    sourcePolicyOverride_preserves (fun key result => (∃ value, VectorResultAllowed key value) → VectorResultAllowed key result)
      sourceVectorChoice sourceVectorChoice_admissible occurrence request reply (fun _ => permitted)
  refine ⟨choices,allowed,?_⟩
  have selected : choices occurrence request = reply := sourcePolicyOverride_selected sourceVectorChoice occurrence request reply
  rw [←selected]
  exact .selected (allowed occurrence request ⟨reply,permitted⟩)

end Exec.Spec

