import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Control.PendingJump
import Exec.Abs.Sim.Typed

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Simulation counts positive SpecTec reductions and explicitly measures all
concrete administrative dispatches. -/
def ConcreteSim (codeLength : Nat) (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : Abs.AState) : Prop :=
  (Abs.decode before = Abs.decode after ∧
    dispatchMeasure afterPending codeLength afterPC after < dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode before) [] (Abs.decode after)

theorem dispatchMeasure_source_any {before after : Abs.AState}
    (beforePending afterPending : Bool) (codeLength pc target : Nat)
    (decrease : Abs.administrativeMeasure after < Abs.administrativeMeasure before) :
    dispatchMeasure afterPending codeLength target after < dispatchMeasure beforePending codeLength pc before := by
  have adjacent : Abs.administrativeMeasure after + 1 ≤ Abs.administrativeMeasure before := decrease
  have multiplied := Nat.mul_le_mul_right (2 * (codeLength + 1)) adjacent
  simp only [Nat.add_mul, Nat.one_mul] at multiplied
  cases beforePending <;> cases afterPending <;>
    simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem ConcreteSim.of_source {before after : Abs.AState}
    (codeLength beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (simulation : Abs.NextSim before after) :
    ConcreteSim codeLength beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | ⟨n, positive, steps⟩
  · exact Or.inl ⟨same, dispatchMeasure_source_any beforePending afterPending codeLength beforePC afterPC decrease⟩
  · exact Or.inr ⟨n, positive, steps⟩

end Itasca.Runtime.Interp
