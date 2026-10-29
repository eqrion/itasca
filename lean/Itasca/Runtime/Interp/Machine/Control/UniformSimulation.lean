import Itasca.Runtime.Interp.Relations.EventfulControl

/-!
A concrete-only rank for silent dispatches. It is independent of source function publication, stack depth, and the size of the current source store.

Main declarations: `silentDispatchPotential` and `UniformConcreteSim`. A direct consumer is `Interp.Machine.Control.UniformSource`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- A concrete-only rank for silent dispatches. It is independent of source
function publication, stack depth, and the size of the current source store. -/
def silentDispatchPotential (pending : Bool) (pc : Nat) : Nat :=
  (if pending then U32.max + 1 else 0) + (U32.max - pc)

theorem silent_dispatch_potential_forward {beforePC afterPC : Nat}
    (forward : beforePC < afterPC) (bound : afterPC ≤ U32.max) :
    silentDispatchPotential false afterPC < silentDispatchPotential false beforePC := by
  simp only [silentDispatchPotential, Bool.false_eq_true, ite_false]
  omega

/-- Stronger dispatch evidence retaining the concrete rank in the silent case.
The ordinary source relation alone cannot imply this extra PC fact. -/
def UniformConcreteSim (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : SourceMachine.AState) (events : List SpecExt.HostEvent) : Prop :=
  (SourceMachine.decode before = SourceMachine.decode after ∧ events = [] ∧
    silentDispatchPotential afterPending afterPC < silentDispatchPotential beforePending beforePC) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)

theorem UniformConcreteSim.forward {beforePC afterPC : Nat} {before after : SourceMachine.AState}
    (same : SourceMachine.decode before = SourceMachine.decode after) (forward : beforePC < afterPC)
    (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] :=
  Or.inl ⟨same, rfl, silent_dispatch_potential_forward forward bound⟩

theorem ConcreteSim.uniform_forward {codeLength beforePC afterPC : Nat} {before after : SourceMachine.AState}
    (simulation : ConcreteSim codeLength beforePC afterPC false false before after)
    (forward : beforePC < afterPC) (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] := by
  rcases simulation with ⟨same,_⟩ | reductions
  · exact .forward same forward bound
  · exact Or.inr reductions

theorem UniformConcreteSim.of_steps {beforePC afterPC beforePending afterPending before after events n}
    (positive : 0 < n) (steps : Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events :=
  Or.inr ⟨n,positive,steps⟩

end Itasca.Runtime.Interp
