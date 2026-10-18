import Exec.Abs.FloatCore.StatePreservation
import Exec.Abs.FloatCore.Correct
import Exec.Abs.FloatCore.Ownership
import Exec.Abs.FloatCore.Bound
import Exec.Abs.FloatCore.Terminal
import Exec.Abs.FloatCore.Extension
import Exec.Abs.FloatCore.Ambient
import Exec.Abs.Float.Transition
namespace Exec.Abs.FloatCore
open SpecExt Exec.Spec Exec.Abs.Ownership

/-- Executable source transitions combine the deterministic mutable core with
the complete float result relation, preserving every permitted NaN result. -/
inductive Step : AState → AResult → Prop where
  | core {before result} (equation : Core.step before = result) (executable : result ≠ .stuck) : Step before result
  | scalar {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Float.Instruction} {result : AResult}
      (transition : Float.Transition ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩
        {f with code := op.source :: after} rest after op result) :
      Step ⟨s,ambient,{f with code := op.source :: after}::rest,[]⟩ result

theorem Step.next_typed {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : FloatCoreState before) : CoreTyped next := by
  cases step with
  | core equation executable => exact (step_correct before next typed covered equation).1
  | scalar transition =>
    have fresh := Float.transition_preservation _ _ _ _ _ _ _ typed.typed transition
    cases transition
    exact ⟨fresh,typed.contents⟩

theorem Step.next_covered {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : FloatCoreState before) : FloatCoreState next := by
  cases step with
  | core equation executable => exact step_covered before next typed.typed covered equation
  | scalar transition =>
    cases transition with
    | next front a b bits values first second effect =>
      apply advance_covered covered rfl
      have frame := covered.active _ (List.mem_cons_self ..)
      exact ⟨fun i member => frame.1 i (List.mem_cons_of_mem _ member),frame.2⟩

theorem Step.next_simulation {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : FloatCoreState before) : NextSim before next := by
  cases step with
  | core equation executable => exact (step_correct before next typed covered equation).2
  | scalar transition => exact Float.transition_simulation _ _ _ _ _ _ _ typed.typed transition

theorem Step.next_owned {bounds : Bounds} {before next : AState}
    (step : Step before (.next next)) (typed : CoreTyped before) (covered : FloatCoreState before)
    (owned : CoreOwned bounds before) : CoreOwned bounds next := by
  cases step with
  | core equation executable => exact step_owned typed covered owned equation
  | @scalar s ambient f rest after op result transition =>
    cases transition with
    | next front a b bits values first second effect =>
      have frame := owned.values.2 {f with code := op.source::after} (List.mem_cons_self ..)
      have remaining : ∀ g ∈ rest, FrameOwned bounds g := fun g member => owned.values.2 g (List.mem_cons_of_mem _ member)
      apply owned_advance (step := rfl) owned.globals (valuesOwned_nil _) ?_ remaining
      refine ⟨frame.1,valuesOwned_append.mpr ⟨?_,?_⟩⟩
      · have original := frame.2
        change ValuesOwned bounds f.vals at original
        change f.vals = front ++ op.operands a b at values
        rw [values] at original
        exact (valuesOwned_append.mp original).1
      · intro value member
        simp only [List.mem_singleton] at member
        subst value
        trivial

theorem Step.next_bound {bound : Nat} {before next : AState}
    (step : Step before (.next next)) (typed : CoreTyped before) (covered : FloatCoreState before)
    (bounded : CodeBound bound before) : CodeBound bound next := by
  cases step with
  | core equation executable => exact step_bound bound before next typed covered bounded equation
  | scalar transition =>
    cases transition with
    | next front a b bits values first second effect =>
      apply advance_bound bounded rfl
      have frame := bounded.frames _ (List.mem_cons_self ..)
      refine ⟨?_,frame.2⟩
      have size := frame.1
      simp at size ⊢
      omega

theorem Step.next_ambient {before next : AState} (step : Step before (.next next)) :
    next.ambient = before.ambient := by
  cases step with
  | core equation executable => exact core_ambient equation
  | scalar transition => cases transition; rfl

theorem Step.next_extends {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : FloatCoreState before) : Extend_store before.store next.store := by
  cases step with
  | core equation executable => exact step_extends before next typed covered equation
  | scalar transition => cases transition; exact extend_store_refl _ typed.typed.store

theorem Step.trap_simulation {before : AState} (step : Step before .trap)
    (typed : CoreTyped before) (covered : FloatCoreState before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | core equation executable => exact step_trap before typed covered equation
  | scalar transition => exact Float.transition_trap_simulation _ _ _ _ _ _ typed.typed transition

theorem Step.not_stuck {before result} (step : Step before result) : result ≠ .stuck := by
  cases step with
  | core equation executable => exact executable
  | scalar transition => cases transition <;> simp [advance]
end Exec.Abs.FloatCore
