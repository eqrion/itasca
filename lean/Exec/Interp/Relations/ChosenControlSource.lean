import Exec.Interp.Relations.ChosenControlPoint
import Exec.Abs.Sim.ChosenTyped
namespace Exec.Interp
open Exec.Spec

theorem ChosenConcreteSim.of_source {choices : SourceChoices} {occurrence : Nat}
    {before after : Abs.AState} (codeLength beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (simulation : Abs.ChosenNextSim choices occurrence before after) :
    ChosenConcreteSim choices occurrence codeLength beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same,decrease⟩ | ⟨n,positive,source⟩
  · exact .inl ⟨same,dispatchMeasure_source_any beforePending afterPending codeLength beforePC afterPC decrease⟩
  · exact .inr ⟨n,positive,source⟩
end Exec.Interp
