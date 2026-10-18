import Exec.Abs.Indirect.Correct
import Exec.Abs.Indirect.Transport
import Exec.Abs.Cumulative.StatePreservation
import Exec.Abs.Cumulative.Correct
import Exec.Abs.Cumulative.Ownership
import Exec.Abs.Cumulative.Bound
import Exec.Abs.Cumulative.Terminal
import Exec.Abs.Cumulative.Extension
import Exec.Abs.FloatCore.Ambient
import Exec.Abs.Cumulative.Heap
import Exec.Abs.Stateful.Bound
import Exec.Abs.Float.Transition
import Exec.Abs.FloatCore.Step
namespace Exec.Abs.Cumulative
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

  | stateful {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Stateful.Instruction} {result : AResult}
      (transition : Stateful.Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
        {f with code := op.source::after} rest after op result)
      (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result

  | indirect {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {table type : Nat} {result : AResult}
      (equation : Indirect.step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
        f rest table type after = result) (executable : result ≠ .stuck) :
      Step ⟨s,ambient,{f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ result

theorem Step.of_float {before result} (step : FloatCore.Step before result) : Step before result := by
  cases step with
  | core equation executable => exact .core equation executable
  | scalar transition => exact .scalar transition

theorem Step.next_typed {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : CumulativeState before) : CoreTyped next := by
  cases step with
  | core equation executable => exact (step_correct before next typed covered equation).1
  | scalar transition =>
    have fresh := Float.transition_preservation _ _ _ _ _ _ _ typed.typed transition
    cases transition
    exact ⟨fresh,typed.contents⟩

  | indirect equation _ => exact Indirect.preservation _ _ _ _ _ _ _ _ typed equation
  | stateful transition _ => exact (Stateful.transition_next _ _ _ _ _ _ _ typed transition).1

theorem Step.next_covered {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : CumulativeState before) : CumulativeState next := by
  cases step with
  | core equation executable => exact step_covered before next typed.typed covered equation
  | scalar transition =>
    cases transition with
    | next front a b bits values first second effect =>
      apply advance_covered covered rfl
      have frame := covered.active _ (List.mem_cons_self ..)
      exact ⟨fun i member => frame.1 i (List.mem_cons_of_mem _ member),frame.2⟩

  | indirect equation _ => exact Indirect.step_covered covered equation
  | @stateful s ambient f rest after op result transition _ =>
    obtain ⟨values,frames,_,_⟩ := Stateful.transition_frame _ _ _ _ _ _ transition
    have functions := Stateful.transition_functions _ _ _ _ _ _ transition
    have active := covered.active {f with code := op.source::after} (List.mem_cons_self ..)
    refine ⟨?_,covered.functions.same functions⟩
    rw [frames]
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun instruction present => active.1 instruction (List.mem_cons_of_mem _ present),active.2⟩
    · exact covered.active item (List.mem_cons_of_mem _ member)

theorem Step.next_simulation {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : CumulativeState before) : NextSim before next := by
  cases step with
  | core equation executable => exact (step_correct before next typed covered equation).2
  | scalar transition => exact Float.transition_simulation _ _ _ _ _ _ _ typed.typed transition

  | indirect equation _ => exact NextSim.counted (Indirect.next_simulation _ _ _ _ _ _ _ _ typed equation) (by decide)
  | stateful transition _ => exact (Stateful.transition_next _ _ _ _ _ _ _ typed transition).2.2

theorem Step.next_owned {bounds : Bounds} {before next : AState}
    (step : Step before (.next next)) (typed : CoreTyped before) (covered : CumulativeState before)
    (owned : StatefulOwned bounds before) : StatefulOwned bounds next := by
  cases step with
  | core equation executable =>
    have fresh := step_owned typed covered owned.core equation
    exact ⟨fresh.values,core_heap_owned owned.heap fresh.globals equation⟩
  | @scalar s ambient f rest after op result transition =>
    cases transition with
    | next front a b bits values first second effect =>
      have frame := owned.values.2 {f with code := op.source::after} (List.mem_cons_self ..)
      have remaining : ∀ g ∈ rest, FrameOwned bounds g := fun g member => owned.values.2 g (List.mem_cons_of_mem _ member)
      apply stateful_owned_advance (step := rfl) owned.heap (valuesOwned_nil _) ?_ remaining
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

  | indirect equation _ => exact Indirect.step_stateful_owned owned equation
  | stateful transition _ => exact stateful_transition_owned _ _ _ _ _ _ _ _ typed owned transition

theorem Step.next_bound {bound : Nat} {before next : AState}
    (step : Step before (.next next)) (typed : CoreTyped before) (covered : CumulativeState before)
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

  | indirect equation _ => exact Indirect.step_bound bounded equation
  | stateful transition _ => exact Stateful.transition_bound _ _ _ _ _ _ _ _ bounded transition

theorem Step.next_ambient {before next : AState} (step : Step before (.next next)) :
    next.ambient = before.ambient := by
  cases step with
  | core equation executable => exact FloatCore.core_ambient equation
  | scalar transition => cases transition; rfl

  | indirect equation _ => exact (Indirect.step_metadata equation).2
  | stateful transition _ =>
    obtain ⟨_,_,ambient,_⟩ := Stateful.transition_frame _ _ _ _ _ _ transition
    exact ambient

theorem Step.next_extends {before next : AState} (step : Step before (.next next))
    (typed : CoreTyped before) (covered : CumulativeState before) : Extend_store before.store next.store := by
  cases step with
  | core equation executable => exact step_extends before next typed covered equation
  | scalar transition => cases transition; exact extend_store_refl _ typed.typed.store

  | indirect equation _ => rw [(Indirect.step_metadata equation).1]; exact extend_store_refl _ typed.typed.store
  | stateful transition _ => exact (Stateful.transition_next _ _ _ _ _ _ _ typed transition).2.1

theorem Step.trap_simulation {before : AState} (step : Step before .trap)
    (typed : CoreTyped before) (covered : CumulativeState before) :
    ∃ n, 0 < n ∧ StepsHN n (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | core equation executable => exact step_trap before typed covered equation
  | scalar transition => exact Float.transition_trap_simulation _ _ _ _ _ _ typed.typed transition

  | indirect equation _ => exact Indirect.trap_simulation _ _ _ _ _ _ _ typed equation
  | stateful transition _ => exact Stateful.transition_trap _ _ _ _ _ _ typed transition

theorem Step.not_stuck {before result} (step : Step before result) : result ≠ .stuck := by
  cases step with
  | core equation executable => exact executable
  | scalar transition => cases transition <;> simp [advance]
  | indirect _ executable => exact executable
  | stateful transition executable => exact executable
end Exec.Abs.Cumulative
