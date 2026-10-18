import Exec.Interp.Core.Outcome
import Exec.Interp.Machines.Slice.SliceErrors
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Every Core integer, control, global, and memory trap has a positive checked source execution to
`TRAP`; boundary and resource failures cannot masquerade as traps. -/
theorem CoreFailure.trap {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {trap : runtime.Trap}
    (failure : CoreFailure allocator hooks exec store platform source (.Trap trap)) :
    CoreTrap trap ∧ ∃ count, 0 < count ∧
      Spec.StepsHN count (Abs.decode source) [] ⟨⟨source.store, source.ambient⟩, [.TRAP]⟩ := by
  rcases failure with ⟨kind, reductions⟩ | ⟨kind, interrupted⟩ | rejected
  · obtain ⟨actual, same, allowed⟩ := kind
    cases same
    exact ⟨allowed, reductions⟩
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    simpa using cause.concrete.kind

/-- No other runtime error class is reachable in the verified Core machine. -/
theorem CoreFailure.kind {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {error : runtime.ExecError}
    (failure : CoreFailure allocator hooks exec store platform source error) :
    (∃ trap, error = .Trap trap ∧ CoreTrap trap) ∨ error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  rcases failure with ⟨kind, _⟩ | ⟨kind, _⟩ | rejected
  · exact Or.inl kind
  · exact Or.inr (Or.inl kind)
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    exact Or.inr cause.concrete.kind

end Exec.Interp
