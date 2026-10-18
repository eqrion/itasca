import Exec.Interp.Relations.ControlPoint

namespace Exec.Interp

/-- A dispatch either consumes administrative potential without emitting an
observable event, or performs positive source reductions with its exact events. -/
def EventfulConcreteSim (codeLength : Nat) (beforePC afterPC : Nat)
    (beforePending afterPending : Bool) (before after : Abs.AState)
    (events : List SpecExt.HostEvent) : Prop :=
  (Abs.decode before = Abs.decode after ∧ events = [] ∧
    dispatchMeasure afterPending codeLength afterPC after <
      dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode before) events (Abs.decode after)

theorem ConcreteSim.eventful {codeLength beforePC afterPC beforePending afterPending before after}
    (simulation : ConcreteSim codeLength beforePC afterPC beforePending afterPending before after) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after [] := by
  rcases simulation with ⟨same,decrease⟩ | reductions
  · exact Or.inl ⟨same,rfl,decrease⟩
  · exact Or.inr reductions

theorem EventfulConcreteSim.empty_iff {codeLength beforePC afterPC beforePending afterPending before after} :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after [] ↔
      ConcreteSim codeLength beforePC afterPC beforePending afterPending before after := by
  constructor
  · intro simulation
    rcases simulation with ⟨same,_,decrease⟩ | reductions
    · exact Or.inl ⟨same,decrease⟩
    · exact Or.inr reductions
  · exact ConcreteSim.eventful

theorem EventfulConcreteSim.of_steps {codeLength beforePC afterPC beforePending afterPending before after events n}
    (positive : 0 < n) (steps : Spec.StepsHN n (Abs.decode before) events (Abs.decode after)) :
    EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events :=
  Or.inr ⟨n,positive,steps⟩

theorem EventfulConcreteSim.source {codeLength beforePC afterPC beforePending afterPending before after events}
    (wellFormed : wf_config (Abs.decode before))
    (simulation : EventfulConcreteSim codeLength beforePC afterPC beforePending afterPending before after events) :
    ∃ n, Spec.StepsHN n (Abs.decode before) events (Abs.decode after) := by
  rcases simulation with ⟨same,rfl,decrease⟩ | ⟨n,positive,steps⟩
  · exact ⟨0,same ▸ Spec.StepsHN.refl wellFormed⟩
  · exact ⟨n,steps⟩
end Exec.Interp
