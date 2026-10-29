import Itasca.Runtime.Interp.Relations.ControlPoint

namespace Itasca.Runtime.Interp

/-- A dispatch either consumes administrative potential without emitting an
observable event, or performs positive source reductions with its exact events. -/
def EventfulConcreteSim (codeLength : Nat) (beforePC afterPC : Nat)
    (beforePending afterPending : Bool) (before after : SourceMachine.AState)
    (events : List SpecExt.HostEvent) : Prop :=
  (SourceMachine.decode before = SourceMachine.decode after ∧ events = [] ∧
    dispatchMeasure afterPending codeLength afterPC after <
      dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)

theorem ConcreteSim.eventful {codeLength beforePC afterPC beforePending afterPending before after}
    (simulation : ConcreteSim codeLength beforePC afterPC beforePending afterPending before after) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after [] := by
  rcases simulation with ⟨same,decrease⟩ | reductions
  · exact Or.inl ⟨same,rfl,decrease⟩
  · exact Or.inr reductions

theorem EventfulConcreteSim.of_steps {codeLength beforePC afterPC beforePending afterPending before after events n}
    (positive : 0 < n) (steps : Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events :=
  Or.inr ⟨n,positive,steps⟩

theorem EventfulConcreteSim.source {codeLength beforePC afterPC beforePending afterPending before after events}
    (wellFormed : wf_config (SourceMachine.decode before))
    (simulation : EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events) :
    ∃ n, Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after) := by
  rcases simulation with ⟨same,rfl,decrease⟩ | ⟨n,positive,steps⟩
  · exact ⟨0,same ▸ Spec.StepsHN.refl wellFormed⟩
  · exact ⟨n,steps⟩
end Itasca.Runtime.Interp
