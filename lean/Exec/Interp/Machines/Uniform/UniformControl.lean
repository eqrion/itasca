import Exec.Interp.Relations.EventfulControl
namespace Exec.Interp
open Aeneas.Std

/-- A concrete-only rank for silent dispatches. It is independent of source
function publication, stack depth, and the size of the current source store. -/
def silentDispatchPotential (pending : Bool) (pc : Nat) : Nat :=
  (if pending then U32.max + 1 else 0) + (U32.max - pc)

theorem silentDispatchPotential_bound (pending : Bool) (pc : Nat) :
    silentDispatchPotential pending pc ≤ 2 * U32.max + 1 := by
  cases pending <;> simp only [silentDispatchPotential, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem silentDispatchPotential_pending (beforePC afterPC : Nat) :
    silentDispatchPotential false afterPC < silentDispatchPotential true beforePC := by
  simp only [silentDispatchPotential, Bool.false_eq_true, ite_false, ite_true]
  omega

theorem silentDispatchPotential_forward {beforePC afterPC : Nat}
    (forward : beforePC < afterPC) (bound : afterPC ≤ U32.max) :
    silentDispatchPotential false afterPC < silentDispatchPotential false beforePC := by
  simp only [silentDispatchPotential, Bool.false_eq_true, ite_false]
  omega

/-- Stronger dispatch evidence retaining the concrete rank in the silent case.
The ordinary source relation alone cannot imply this extra PC fact. -/
def UniformConcreteSim (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : Abs.AState) (events : List SpecExt.HostEvent) : Prop :=
  (Abs.decode before = Abs.decode after ∧ events = [] ∧
    silentDispatchPotential afterPending afterPC < silentDispatchPotential beforePending beforePC) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode before) events (Abs.decode after)

theorem UniformConcreteSim.pending (beforePC afterPC : Nat) (state : Abs.AState) :
    UniformConcreteSim beforePC afterPC true false state state [] :=
  Or.inl ⟨rfl, rfl, silentDispatchPotential_pending _ _⟩

theorem UniformConcreteSim.forward {beforePC afterPC : Nat} {before after : Abs.AState}
    (same : Abs.decode before = Abs.decode after) (forward : beforePC < afterPC)
    (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] :=
  Or.inl ⟨same, rfl, silentDispatchPotential_forward forward bound⟩

theorem UniformConcreteSim.of_source_forward {beforePC afterPC : Nat} {before after : Abs.AState}
    (simulation : Abs.NextSim before after) (forward : beforePC < afterPC)
    (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] := by
  rcases simulation with ⟨same,_⟩ | reductions
  · exact .forward same forward bound
  · exact Or.inr reductions

theorem ConcreteSim.uniform_forward {codeLength beforePC afterPC : Nat} {before after : Abs.AState}
    (simulation : ConcreteSim codeLength beforePC afterPC false false before after)
    (forward : beforePC < afterPC) (bound : afterPC ≤ U32.max) :
    UniformConcreteSim beforePC afterPC false false before after [] := by
  rcases simulation with ⟨same,_⟩ | reductions
  · exact .forward same forward bound
  · exact Or.inr reductions

theorem UniformConcreteSim.of_steps {beforePC afterPC beforePending afterPending before after events n}
    (positive : 0 < n) (steps : Spec.StepsHN n (Abs.decode before) events (Abs.decode after)) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events :=
  Or.inr ⟨n,positive,steps⟩

/-- Administrative source normalization changes neither concrete PC nor phase.
Positive normalization is paid for; empty normalization retains the rank. -/
theorem UniformConcreteSim.prepend {beforePC afterPC beforePending afterPending before middle after events}
    (normal : Spec.StepsHN 0 (Abs.decode before) [] (Abs.decode middle))
    (step : UniformConcreteSim beforePC afterPC beforePending afterPending middle after events) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after events := by
  simpa only [UniformConcreteSim, normal.zero.1] using step

theorem UniformConcreteSim.prepend_steps {beforePC afterPC beforePending afterPending before middle after events rest n}
    (normal : Spec.StepsHN n (Abs.decode before) events (Abs.decode middle))
    (step : UniformConcreteSim beforePC afterPC beforePending afterPending middle after rest) :
    UniformConcreteSim beforePC afterPC beforePending afterPending before after (events ++ rest) := by
  by_cases zero : n = 0
  · subst n
    obtain ⟨same, rfl⟩ := normal.zero
    simpa only [UniformConcreteSim, same, List.nil_append] using step
  · rcases step with ⟨same, rfl, _⟩ | ⟨count, positive, reductions⟩
    · exact Or.inr ⟨n, by omega, by simpa only [same, List.append_nil] using normal⟩
    · exact Or.inr ⟨n+count, by omega, normal.trans reductions⟩

end Exec.Interp

