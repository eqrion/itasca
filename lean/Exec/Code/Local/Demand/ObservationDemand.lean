import Itasca.Visitor.Recording

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca VisitorTrace

/-- Source-only temporary-storage demand of one validated observation. Compiler
code, emitted slots, and compiler success do not occur in this definition. -/
structure ObservationDemand where
  operands : Nat
  controls : Nat
  locals : Nat

def eventDemand : Event → ObservationDemand
  | .functionStart ctx _ _ _ => ⟨0,0,ctx.locals.length⟩
  | .op state _ => ⟨state.vals.length,state.ctrls.length,0⟩

def ObservationDemand.join (left right : ObservationDemand) : ObservationDemand :=
  ⟨max left.operands right.operands,max left.controls right.controls,max left.locals right.locals⟩

/-- Componentwise maximum of independently validated callback-state sizes.
A complete compiler theorem must construct this reference log using validator
completeness, rather than require an accepted compiler log from its caller. -/
def observationDemand : List Observation → ObservationDemand
  | [] => ⟨0,0,0⟩
  | observation :: rest => (eventDemand observation.event).join (observationDemand rest)

theorem observationDemand.member {log : List Observation} {observation : Observation}
    (member : observation ∈ log) :
    (eventDemand observation.event).operands ≤ (observationDemand log).operands ∧
    (eventDemand observation.event).controls ≤ (observationDemand log).controls ∧
    (eventDemand observation.event).locals ≤ (observationDemand log).locals := by
  induction log with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Nat.le_max_left _ _,Nat.le_max_left _ _,Nat.le_max_left _ _⟩
    · obtain ⟨values,controls,locals⟩ := ih member
      exact ⟨values.trans (Nat.le_max_right _ _),controls.trans (Nat.le_max_right _ _),
        locals.trans (Nat.le_max_right _ _)⟩

/-- Any source observation retained in the final reference log has bounded
operand and control vectors. An already recorded prefix can be discarded. -/
theorem observationDemand.recorded_op {prior suffix final : List Observation}
    {state : code.OpIterState} {action : Action} {reply : VisitResult}
    (recorded : final = prior ++ ⟨.op state action,reply⟩ :: suffix) :
    state.vals.length ≤ (observationDemand final).operands ∧
    state.ctrls.length ≤ (observationDemand final).controls := by
  have member : (⟨.op state action,reply⟩ : Observation) ∈ final := by
    rw [recorded]
    simp
  exact ⟨(observationDemand.member member).1,(observationDemand.member member).2.1⟩

end Itasca.Runtime.Code
