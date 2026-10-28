import Itasca.Runtime.Theorems.Composition.Cumulative.CumulativeExecutionOutcome
import Itasca.Runtime.Interp.Machines.Slice.SliceErrors
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- Every Core integer, control, global, and memory trap has a positive checked source execution to
`TRAP`; boundary and resource failures cannot masquerade as traps. -/
theorem CumulativeFailure.trap {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {trap : runtime.Trap}
    (failure : CumulativeFailure allocator hooks exec store platform source (.Trap trap)) :
    CumulativeTrap trap ∧ ∃ count, 0 < count ∧
      Spec.StepsHN count (Abs.decode source) [] ⟨⟨source.store, source.ambient⟩, [.TRAP]⟩ := by
  rcases failure with ⟨kind, reductions⟩ | ⟨kind, interrupted⟩ | rejected
  · obtain ⟨actual, same, allowed⟩ := kind
    cases same
    exact ⟨allowed, reductions⟩
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · simpa using direct.concrete.kind
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      simpa using cause.kind

/-- No other runtime error class is reachable in the verified Core machine. -/
theorem CumulativeFailure.kind {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {error : runtime.ExecError}
    (failure : CumulativeFailure allocator hooks exec store platform source error) :
    (∃ trap, error = .Trap trap ∧ CumulativeTrap trap) ∨ error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  rcases failure with ⟨kind, _⟩ | ⟨kind, _⟩ | rejected
  · exact Or.inl kind
  · exact Or.inr (Or.inl kind)
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    rcases cause with direct | ⟨code,indirect⟩
    · exact Or.inr direct.concrete.kind
    · obtain ⟨entry,selector,offset,table,type,pc,address,base,function,ii,fi,inst,callee,fetch,pair,found,defined,hi,hc,baseEq,pcEq,cause,site⟩ := indirect
      exact Or.inr cause.kind

end Itasca.Runtime.Theorems
