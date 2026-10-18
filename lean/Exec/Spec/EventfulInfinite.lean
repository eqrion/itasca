import Exec.Spec.InfiniteSource

namespace Exec.Spec
open SpecExt

/-- A coherent infinite source execution retaining the events in every positive
chunk. Empty event lists remain possible for arbitrarily long executions. -/
def InfiniteSourceWithEvents (initial : config) : Prop :=
  ∃ states : Nat → config, ∃ events : Nat → List HostEvent,
    states 0 = initial ∧ ∀ n, ∃ count, 0 < count ∧
      StepsHN count (states n) (events n) (states (n+1))

theorem InfiniteSource.with_events {initial : config} (infinite : InfiniteSource initial) :
    InfiniteSourceWithEvents initial := by
  obtain ⟨states,first,edges⟩ := infinite
  exact ⟨states,fun _ => [],first,edges⟩

theorem InfiniteSourceWithEvents.prepend {initial next : config} {events : List HostEvent}
    (infinite : InfiniteSourceWithEvents next) (steps : StepsH initial events next) :
    InfiniteSourceWithEvents initial := by
  obtain ⟨states,trace,first,edges⟩ := infinite
  obtain ⟨prefixCount,prefixSteps⟩ := stepsH_count steps
  refine ⟨(fun n => match n with | 0 => initial | n+1 => states (n+1)),
    (fun n => match n with | 0 => events ++ trace 0 | n+1 => trace (n+1)),rfl,?_⟩
  intro n
  cases n with
  | zero =>
    obtain ⟨count,positive,edge⟩ := edges 0
    rw [first] at edge
    exact ⟨prefixCount+count,by omega,by simpa using prefixSteps.trans edge⟩
  | succ n => exact edges (n+1)

/-- Conditional simulation plumbing: total concrete successors and strict
administrative decrease yield a positive source chunk with a real finite
concrete history. No fixed bound on future host-published code is assumed. -/
theorem positive_history_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) :
    ∃ after events dispatches count, 0 < dispatches ∧
      Iterations next dispatches initial events after ∧ 0 < count ∧
      StepsHN count (decode initial) events (decode after) := by
  have bounded : ∀ budget s, potential s ≤ budget →
      ∃ after events dispatches count, 0 < dispatches ∧
        Iterations next dispatches s events after ∧ 0 < count ∧
        StepsHN count (decode s) events (decode after) := by
    intro budget
    induction budget with
    | zero =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨same,empty,decrease⟩ | ⟨count,positive,steps⟩
      · omega
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,steps⟩
    | succ budget ih =>
      intro s bound
      obtain ⟨events,after,edge⟩ := successor s
      rcases simulation s events after edge with ⟨same,rfl,decrease⟩ | ⟨count,positive,steps⟩
      · obtain ⟨last,trace,dispatches,count,nonempty,history,positive,steps⟩ := ih after (by omega)
        exact ⟨last,trace,dispatches+1,count,by omega,by simpa using Iterations.cons edge history,
          positive,by simpa only [same] using steps⟩
      · exact ⟨after,events,1,count,by omega,by simpa using Iterations.cons edge (.refl after),positive,steps⟩
  exact bounded (potential initial) initial (Nat.le_refl _)

/-- The infinite source chunks are backed by consecutive histories of `next`.
A runtime application must establish `successor` and `simulation` from its
actual loop; this lemma alone makes no claim about interpreter execution. -/
theorem infinite_histories_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) :
    ∃ states : Nat → S, ∃ events : Nat → List HostEvent,
      states 0 = initial ∧ ∀ n, ∃ dispatches count, 0 < dispatches ∧
        Iterations next dispatches (states n) (events n) (states (n+1)) ∧
        0 < count ∧ StepsHN count (decode (states n)) (events n) (decode (states (n+1))) := by
  classical
  have advance := positive_history_of_decreasing_stutter next decode potential successor simulation
  let stateAfter (s : S) : S := Classical.choose (advance s)
  let traceAfter (s : S) : List HostEvent := Classical.choose (Classical.choose_spec (advance s))
  let states : Nat → S := fun n => Nat.rec initial (fun _ previous => stateAfter previous) n
  refine ⟨states,fun n => traceAfter (states n),rfl,?_⟩
  intro n
  exact Classical.choose_spec (Classical.choose_spec (advance (states n)))

theorem infinite_source_of_decreasing_stutter {S : Type}
    (next : S → List HostEvent → S → Prop) (decode : S → config) (potential : S → Nat)
    (successor : ∀ s, ∃ events after, next s events after)
    (simulation : ∀ s events after, next s events after →
      (decode s = decode after ∧ events = [] ∧ potential after < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode after))
    (initial : S) : InfiniteSourceWithEvents (decode initial) := by
  obtain ⟨states,events,first,edges⟩ :=
    infinite_histories_of_decreasing_stutter next decode potential successor simulation initial
  refine ⟨fun n => decode (states n),events,congrArg decode first,?_⟩
  intro n
  obtain ⟨dispatches,count,nonempty,history,positive,steps⟩ := edges n
  exact ⟨count,positive,steps⟩
end Exec.Spec
