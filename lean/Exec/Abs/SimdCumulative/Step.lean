import Exec.Abs.SimdSupported
import Exec.Abs.Supported.CumulativeStep

namespace Exec.Abs.SimdCumulative
open SpecExt Exec.Spec Ownership

/-- The combined source relation preserves every result admitted by scalar and
    SIMD semantics, including floating-point choices and memory bounds traps. -/
inductive Step : AState → AResult → Prop where
  | cumulative {before result} : Cumulative.Step before result → Step before result
  | simd {before result} : Simd.Step before result → Step before result

theorem Step.next_typed {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : SimdCumulativeState before) : CoreTyped next := by
  cases step with
  | cumulative old => exact old.next_typed_supported simd_cumulative_language typed covered
  | simd next => exact next.next_typed typed

theorem Step.next_covered {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : SimdCumulativeState before) : SimdCumulativeState next := by
  cases step with
  | cumulative old => exact old.next_covered_supported simd_cumulative_language typed covered
  | simd next => exact next.next_supported covered

theorem Step.next_simulation {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : SimdCumulativeState before) : NextSim before next := by
  cases step with
  | cumulative old => exact old.next_simulation_supported simd_cumulative_language typed covered
  | simd next => exact next.next_simulation typed

theorem Step.next_owned {before next : AState} {bounds : Bounds} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : SimdCumulativeState before)
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | cumulative old => exact old.next_owned_supported simd_cumulative_language typed covered owned
  | simd next => exact next.next_owned owned

theorem Step.next_bound {before next : AState} {bound : Nat} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : SimdCumulativeState before)
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | cumulative old => exact old.next_bound_supported simd_cumulative_language typed covered bounded
  | simd next => exact next.next_bound bounded

theorem Step.next_ambient {before next : AState} (step : Step before (.next next)) :
    next.ambient = before.ambient := by
  cases step with
  | cumulative old => exact old.next_ambient
  | simd next => exact next.next_ambient

theorem Step.next_extends {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : SimdCumulativeState before) : Extend_store before.store next.store := by
  cases step with
  | cumulative old => exact old.next_extends_supported simd_cumulative_language typed covered
  | simd next => exact next.next_extension typed

theorem Step.trap_simulation {before : AState} (step : Step before .trap)
    (typed : CoreTyped before) (covered : SimdCumulativeState before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | cumulative old => exact old.trap_simulation_supported simd_cumulative_language typed covered
  | simd next => exact next.trap_simulation typed

theorem Step.not_stuck {before : AState} {result : AResult} (step : Step before result) : result ≠ .stuck := by
  cases step with
  | cumulative old => exact old.not_stuck
  | simd next =>
    cases next with
    | pure => intro impossible; cases impossible
    | constant => intro impossible; cases impossible
    | memory signature transition => cases transition <;> intro impossible <;> cases impossible
end Exec.Abs.SimdCumulative
