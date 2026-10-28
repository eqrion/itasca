import Itasca.Runtime.Spec.Steps
import Itasca.Runtime.Spec.Context
import Mathlib.Tactic

/-! Counted extended reductions for quantitative execution simulation. These
lemmas count specification steps, not interpreter dispatches. The generic
simulation theorem below still requires a per-dispatch proof and a bounded
administrative measure; it makes no claim about the Rust interpreter by itself. -/

namespace Itasca.Runtime.Spec
open SpecExt

inductive StepsHN : Nat → config → List HostEvent → config → Prop where
  | refl {c : config} : wf_config c → StepsHN 0 c [] c
  | cons {n : Nat} {c c' c'' : config} {events rest : List HostEvent} :
      StepH c events c' → StepsHN n c' rest c'' →
      StepsHN (n + 1) c (events ++ rest) c''

theorem StepsHN.erase {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') : StepsH c events c' := by
  induction h with
  | refl h => exact .refl h
  | cons h _ ih => exact .cons h ih

theorem StepsHN.trans {n m : Nat} {c c' c'' : config} {events rest : List HostEvent}
    (h : StepsHN n c events c') (h' : StepsHN m c' rest c'') :
    StepsHN (n + m) c (events ++ rest) c'' := by
  induction h with
  | refl _ => simpa using h'
  | cons h _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using StepsHN.cons h (ih h')

theorem StepsHN.map {wrap : config → config}
    (hw : ∀ c, wf_config c → wf_config (wrap c))
    (hs : ∀ c events c', StepH c events c' → StepH (wrap c) events (wrap c'))
    {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') : StepsHN n (wrap c) events (wrap c') := by
  induction h with
  | refl h => exact .refl (hw _ h)
  | cons h _ ih => exact .cons (hs _ _ _ h) ih

theorem StepsHN.zero {c c' : config} {events : List HostEvent}
    (h : StepsHN 0 c events c') : c = c' ∧ events = [] := by
  cases h
  exact ⟨rfl, rfl⟩

theorem stepsH_count {c c' : config} {events : List HostEvent}
    (h : StepsH c events c') : ∃ n, StepsHN n c events c' := by
  induction h with
  | refl h => exact ⟨0, .refl h⟩
  | cons h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .cons h hn⟩

/-- A finite machine run carrying the events from each dispatch. -/
inductive Iterations {S : Type} (next : S → List HostEvent → S → Prop) :
    Nat → S → List HostEvent → S → Prop where
  | refl (s : S) : Iterations next 0 s [] s
  | cons {n : Nat} {s s' s'' : S} {events rest : List HostEvent} :
      next s events s' → Iterations next n s' rest s'' →
      Iterations next (n + 1) s (events ++ rest) s''

end Itasca.Runtime.Spec
