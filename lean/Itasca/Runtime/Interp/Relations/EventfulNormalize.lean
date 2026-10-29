import Itasca.Runtime.Interp.Relations.EventfulControl
import Itasca.Runtime.Interp.Control.NormalizeCompose

namespace Itasca.Runtime.Interp

theorem EventfulConcreteSim.trans
    {codeLength firstPC middlePC lastPC firstPending middlePending lastPending before middle after events rest}
    (first : EventfulConcreteSim codeLength firstPC middlePC firstPending middlePending before middle events)
    (second : EventfulConcreteSim codeLength middlePC lastPC middlePending lastPending middle after rest) :
    EventfulConcreteSim codeLength firstPC lastPC firstPending lastPending before after (events ++ rest) := by
  rcases first with ⟨firstEq,rfl,firstDecrease⟩ | ⟨n,hn,firstSteps⟩
  · rcases second with ⟨secondEq,rfl,secondDecrease⟩ | ⟨m,hm,secondSteps⟩
    · exact Or.inl ⟨firstEq.trans secondEq,rfl,Nat.lt_trans secondDecrease firstDecrease⟩
    · exact Or.inr ⟨m,hm,by simpa only [List.nil_append,firstEq] using secondSteps⟩
  · rcases second with ⟨secondEq,rfl,secondDecrease⟩ | ⟨m,hm,secondSteps⟩
    · exact Or.inr ⟨n,hn,by simpa only [List.append_nil,secondEq] using firstSteps⟩
    · exact Or.inr ⟨n+m,by omega,firstSteps.trans secondSteps⟩

/-- Normalize erased source control before a dispatch while retaining exactly
that dispatch's events, including a host call reached through nested blocks. -/
theorem EventfulConcreteSim.prepend_normalization {count before middle}
    (chain : ErasedSteps count before middle) (s : store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s,ambient,before::rest,[]⟩)
    {codeLength pc target pending after events}
    (simulation : EventfulConcreteSim codeLength pc target false pending
      ⟨s,ambient,middle::rest,[]⟩ after events) :
    EventfulConcreteSim codeLength pc target false pending ⟨s,ambient,before::rest,[]⟩ after events := by
  rcases (chain.sound s ambient rest typed).2 with ⟨_,same⟩ | prefixSimulation
  · simpa only [same] using simulation
  · simpa only [List.nil_append] using
      (ConcreteSim.of_source codeLength pc pc false false prefixSimulation).eventful.trans simulation
end Itasca.Runtime.Interp
