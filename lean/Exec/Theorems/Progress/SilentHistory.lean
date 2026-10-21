import Exec.Spec.Counted

/-! Shared finite-history induction for machines with a silent continuation
step. Machine-specific proofs establish that step and retain their own laws. -/
namespace Exec.Theorems
open SpecExt

/-- A predicate with a silent successor has finite histories of every length.
No machine, platform, instruction-set or normal-return premise is added. -/
theorem silent_history {S : Type} {next : S → List HostEvent → S → Prop}
    {continues : S → Prop}
    (advance : ∀ state, continues state → ∃ following, next state [] following ∧ continues following)
    (count : Nat) (initial : S) (held : continues initial) :
    ∃ final, Spec.Iterations next count initial [] final ∧ continues final := by
  induction count generalizing initial with
  | zero => exact ⟨initial,.refl initial,held⟩
  | succ count ih =>
    obtain ⟨following,step,kept⟩ := advance initial held
    obtain ⟨final,history,finished⟩ := ih following kept
    exact ⟨final,Spec.Iterations.cons step history,finished⟩
end Exec.Theorems
