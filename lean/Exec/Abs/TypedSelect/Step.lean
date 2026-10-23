import Exec.Abs.TypedSelect.Correct
import Exec.Abs.Supported.PureCoverage
import Exec.Abs.Ownership.Core
import Exec.Abs.Core.Bound
import Exec.Abs.Stateful.OwnershipPrimitives

namespace Exec.Abs.TypedSelect
open SpecExt Exec.Spec Exec.Abs.Ownership

/-- Explicit select uses the deterministic value choice, with the type
annotation retained in its source configuration. -/
inductive Step : AState → AState → Prop where
  | next {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {declared : valtype} {after : List instr} {next : AState}
      (equation : Core.select ⟨s,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩
        f rest after = .next next) :
      Step ⟨s,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩ next

theorem Step.correct {before next} (step : Step before next) (typed : CoreTyped before) :
    CoreTyped next ∧ StepH (decode before) [] (decode next) := by
  cases step with
  | next equation =>
    obtain ⟨actual,run,fresh,simulation⟩ := progress _ _ _ _ _ _ typed
    have same := AResult.next.inj (equation.symm.trans run)
    subst actual
    exact ⟨fresh,simulation⟩

theorem Step.next_supported {before next}
    (step : Step before next) (covered : SupportedState before) : SupportedState next := by
  cases step with
  | next equation =>
    have frame := covered.active _ (List.mem_cons_self ..)
    simp only [Core.select] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply Supported.advance_covered covered equation
      exact ⟨fun i member => frame.1 i (List.mem_cons_of_mem _ member),frame.2⟩

theorem Step.next_bound {bound before next} (step : Step before next)
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | next equation =>
    have frame := bounded.frames _ (List.mem_cons_self ..)
    simp only [Core.select] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply advance_bound bounded equation
      refine ⟨?_,frame.2⟩
      have size := frame.1
      simp at size ⊢
      omega

theorem Step.next_owned {bounds before next} (step : Step before next)
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | @next s ambient f rest declared after next equation =>
    have frame := owned.values.2 _ (List.mem_cons_self ..)
    have remaining : ∀ g ∈ rest, FrameOwned bounds g :=
      fun g member => owned.values.2 g (List.mem_cons_of_mem _ member)
    simp only [Core.select] at equation
    repeat' first | split at equation | contradiction
    all_goals
      apply stateful_owned_advance (step := equation) owned.heap (valuesOwned_nil _) ?_ remaining
      refine ⟨frame.1,?_⟩
      have values := frame.2
      aesop (add safe forward ValuesOwned.pop)

end Exec.Abs.TypedSelect
