import Exec.Abs.Sim.Step
import Exec.Abs.Bound

namespace Exec.Abs
open SpecExt Exec.Spec

/-- Actual successful abstract transitions, with the empty event trace of this
host-free slice. Typing and source reduction are conclusions, not premises. -/
def SuccessfulStep (s : AState) (events : List HostEvent) (next : AState) : Prop :=
  events = [] ∧ astep s = .next next

/-- Compose simulations while deriving all intermediate invariants from the
initial state. A source step pays for at most `bound + 1` abstract iterations. -/
theorem run_simulation (bound : Nat) {n : Nat} {s next : AState} {events : List HostEvent}
    (run : Iterations SuccessfulStep n s events next)
    (typed : ATyped s) (slice : SliceState s) (bounded : CodeBound bound s) :
    ∃ count, StepsHN count (decode s) events (decode next) ∧
      n + administrativeMeasure next ≤ administrativeMeasure s + (bound + 1) * count := by
  induction run with
  | refl s => exact ⟨0, .refl typed.decode_wf, by simp⟩
  | @cons n s middle last events tail step run ih =>
    obtain ⟨rfl, step⟩ := step
    have typed' := astep_preservation s middle typed slice step
    have slice' := astep_slice s middle typed slice step
    have bounded' := astep_bound bound s middle typed slice bounded step
    obtain ⟨count, hc, hz⟩ := astep_counted s middle typed slice step
    have cost : 1 + administrativeMeasure middle ≤ administrativeMeasure s + (bound + 1) * count := by
      by_cases zero : count = 0
      · have decrease := hz zero
        simp only [zero, Nat.mul_zero, Nat.add_zero]
        omega
      · have positive : 0 < count := by omega
        have hm := Nat.le_mul_of_pos_right (bound + 1) positive
        have hb := bounded'.measure
        omega
    obtain ⟨rest, hr, hp⟩ := ih typed' slice' bounded'
    refine ⟨count + rest, hc.trans hr, ?_⟩
    rw [Nat.mul_add]
    omega

/-- A fixed initial syntactic bound excludes silent divergence: every
`sizeOf initial + 1` successful abstract transitions force a source step.
The bound remains fixed across arbitrary recursive calls and branch cycles. -/
theorem run_progress {n : Nat} {s next : AState} {events : List HostEvent}
    (run : Iterations SuccessfulStep n s events next)
    (typed : ATyped s) (slice : SliceState s) :
    ∃ count, StepsHN count (decode s) events (decode next) ∧
      n / (sizeOf s + 1) ≤ count := by
  have bounded := codeBound_initial s
  obtain ⟨count, hc, hp⟩ := run_simulation (sizeOf s) run typed slice bounded
  refine ⟨count, hc, ?_⟩
  have hb := bounded.measure
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  rw [Nat.succ_mul, Nat.mul_comm count]
  omega

end Exec.Abs
