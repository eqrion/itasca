import Exec.Interp.Machines.Uniform.UniformControl
import Exec.Abs.Core.PositiveControl
namespace Itasca.Runtime.Interp
open Aeneas.Std SpecExt Itasca.Runtime.Spec

/-- An unchanged source state cancels the old source potential. Hence an
ordinary-phase silent dispatch must move forward, independent of code size. -/
theorem ConcreteSim.uniform_same {codeLength beforePC afterPC : Nat}
    {pending : Bool} {source : Abs.AState}
    (simulation : ConcreteSim codeLength beforePC afterPC false pending source source)
    (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false pending source source [] := by
  rcases simulation with ⟨same,decrease⟩ | reductions
  · cases pending with
    | false =>
      have forward : beforePC < afterPC := by
        simp only [dispatchMeasure, Bool.false_eq_true, ite_false] at decrease
        omega
      exact UniformConcreteSim.forward rfl forward bound
    | true =>
      simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] at decrease
      omega
  · exact Or.inr reductions

theorem UniformConcreteSim.single {beforePC afterPC beforePending afterPending before after events}
    (step : StepH (Abs.decode before) events (Abs.decode after)) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events :=
  .of_steps (by omega : 0 < 1)
    (by simpa only [List.append_nil] using StepsHN.cons step (StepsHN.refl (stepH_wf step).2))
end Itasca.Runtime.Interp
