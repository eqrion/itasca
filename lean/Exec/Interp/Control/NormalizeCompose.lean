import Exec.Interp.Control.NormalizeClosure
import Exec.Interp.Relations.ControlPoint

namespace Itasca.Runtime.Interp

theorem ConcreteSim.trans {codeLength firstPC middlePC lastPC firstPending middlePending lastPending before middle after}
    (first : ConcreteSim codeLength firstPC middlePC firstPending middlePending before middle)
    (second : ConcreteSim codeLength middlePC lastPC middlePending lastPending middle after) :
    ConcreteSim codeLength firstPC lastPC firstPending lastPending before after := by
  rcases first with ⟨firstEq, firstDecrease⟩ | ⟨n, hn, firstSteps⟩
  · rcases second with ⟨secondEq, secondDecrease⟩ | ⟨m, hm, secondSteps⟩
    · exact Or.inl ⟨firstEq.trans secondEq, Nat.lt_trans secondDecrease firstDecrease⟩
    · exact Or.inr ⟨m, hm, by simpa only [firstEq] using secondSteps⟩
  · rcases second with ⟨secondEq, secondDecrease⟩ | ⟨m, hm, secondSteps⟩
    · exact Or.inr ⟨n, hn, by simpa only [secondEq] using firstSteps⟩
    · exact Or.inr ⟨n + m, by omega, by simpa using firstSteps.trans secondSteps⟩

/-- Source-only normalization can precede the real dispatch without losing
its measured stutter or positive counted reduction guarantee. -/
theorem ConcreteSim.prepend_normalization {count before middle} (chain : ErasedSteps count before middle)
    (s : store) (ambient : frame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    {codeLength pc target pending after}
    (simulation : ConcreteSim codeLength pc target false pending
      ⟨s, ambient, middle :: rest, []⟩ after) :
    ConcreteSim codeLength pc target false pending ⟨s, ambient, before :: rest, []⟩ after := by
  rcases (chain.sound s ambient rest typed).2 with ⟨_, same⟩ | prefixSimulation
  · simpa only [same] using simulation
  · exact (ConcreteSim.of_source codeLength pc pc false false prefixSimulation).trans simulation

end Itasca.Runtime.Interp
