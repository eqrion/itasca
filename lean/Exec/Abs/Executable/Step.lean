import Exec.Abs.Executable
import Exec.Abs.TypedSelect.Step
import Exec.Abs.BrTableTransition
import Exec.Abs.Supported.CumulativeStep

namespace Exec.Abs.Executable
open SpecExt Exec.Spec Ownership

/-- The combined source relation preserves every result admitted by scalar and
    SIMD semantics, including floating-point choices and memory bounds traps. -/
inductive Step : AState → AResult → Prop where
  | cumulative {before result} : Cumulative.Step before result → Step before result
  | simd {before result} : Simd.Step before result → Step before result
  | typedSelect {before next} : TypedSelect.Step before next → Step before (.next next)
  | branchTable {before next} : BrTable.Transition before next → Step before (.next next)

theorem Step.next_typed {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) : CoreTyped next := by
  cases step with
  | cumulative old => exact old.next_typed_supported executable_language typed covered
  | simd next => exact next.next_typed typed
  | typedSelect next => exact (next.correct typed).1
  | branchTable next => exact (next.correct typed).1

theorem Step.next_covered {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) : ExecutableState next := by
  cases step with
  | cumulative old => exact old.next_covered_supported executable_language typed covered
  | simd next => exact next.next_supported covered
  | typedSelect next => exact next.next_supported covered
  | branchTable next => exact next.next_supported executable_language covered

theorem Step.next_simulation {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) : NextSim before next := by
  cases step with
  | cumulative old => exact old.next_simulation_supported executable_language typed covered
  | simd next => exact next.next_simulation typed
  | typedSelect next => exact NextSim.single (next.correct typed).2
  | branchTable next => exact (next.correct typed).2

theorem Step.next_owned {before next : AState} {bounds : Bounds} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before)
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | cumulative old => exact old.next_owned_supported executable_language typed covered owned
  | simd next => exact next.next_owned owned
  | typedSelect next => exact next.next_owned owned
  | branchTable next => exact next.next_owned owned

theorem Step.next_bound {before next : AState} {bound : Nat} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before)
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | cumulative old => exact old.next_bound_supported executable_language typed covered bounded
  | simd next => exact next.next_bound bounded
  | typedSelect next => exact next.next_bound bounded
  | branchTable next => exact next.next_bound bounded

theorem Step.next_ambient {before next : AState} (step : Step before (.next next)) :
    next.ambient = before.ambient := by
  cases step with
  | cumulative old => exact old.next_ambient
  | simd next => exact next.next_ambient
  | typedSelect next => exact next.metadata.2
  | branchTable next => exact next.metadata.2

theorem Step.next_extends {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) : Extend_store before.store next.store := by
  cases step with
  | cumulative old => exact old.next_extends_supported executable_language typed covered
  | simd next => exact next.next_extension typed
  | typedSelect next => exact next.next_extends typed
  | branchTable next => rw [next.metadata.1]; exact extend_store_refl _ typed.typed.store

theorem Step.trap_simulation {before : AState} (step : Step before .trap)
    (typed : CoreTyped before) (covered : ExecutableState before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | cumulative old => exact old.trap_simulation_supported executable_language typed covered
  | simd next => exact next.trap_simulation typed

theorem Step.not_stuck {before : AState} {result : AResult} (step : Step before result) : result ≠ .stuck := by
  cases step with
  | cumulative old => exact old.not_stuck
  | typedSelect _ => intro impossible; cases impossible
  | branchTable _ => intro impossible; cases impossible
  | simd next =>
    cases next with
    | pure => intro impossible; cases impossible
    | constant => intro impossible; cases impossible
    | memory signature transition => cases transition <;> intro impossible <;> cases impossible
end Exec.Abs.Executable
