import Exec.Spec.Steps
import Exec.Spec.Context
import Mathlib.Tactic

/-! Counted extended reductions for quantitative execution simulation. These
lemmas count specification steps, not interpreter dispatches. The generic
simulation theorem below still requires a per-dispatch proof and a bounded
administrative measure; it makes no claim about the Rust interpreter by itself. -/

namespace Exec.Spec
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

/-- Compose a local quantitative simulation. One machine iteration consumes
one unit of potential or pays for it with specification reductions. -/
theorem iterations_simulation {S : Type} {next : S → List HostEvent → S → Prop}
    (decode : S → config) (potential : S → Nat) (cost : Nat)
    (hw : ∀ s, wf_config (decode s))
    (step : ∀ s events s', next s events s' →
      ∃ count, StepsHN count (decode s) events (decode s') ∧
        1 + potential s' ≤ potential s + cost * count)
    {n : Nat} {s s' : S} {events : List HostEvent}
    (run : Iterations next n s events s') :
    ∃ count, StepsHN count (decode s) events (decode s') ∧
      n + potential s' ≤ potential s + cost * count := by
  induction run with
  | refl s => exact ⟨0, .refl (hw s), by simp⟩
  | cons h _ ih =>
    obtain ⟨count, hc, hp⟩ := step _ _ _ h
    obtain ⟨rest, hr, hp'⟩ := ih
    refine ⟨count + rest, hc.trans hr, ?_⟩
    rw [Nat.mul_add]
    omega

/-- A bounded decreasing stutter measure gives the quantitative bound needed
for no-silent-divergence: every `bound + 1` iterations require a spec step.
The caller must prove that each dispatch either reduces the measure without
changing its decoded state, or performs a positive number of reductions. -/
theorem iterations_progress {S : Type} {next : S → List HostEvent → S → Prop}
    (decode : S → config) (potential : S → Nat) (bound : Nat)
    (hw : ∀ s, wf_config (decode s)) (hb : ∀ s, potential s ≤ bound)
    (step : ∀ s events s', next s events s' →
      (decode s = decode s' ∧ events = [] ∧ potential s' < potential s) ∨
      ∃ count, 0 < count ∧ StepsHN count (decode s) events (decode s'))
    {n : Nat} {s s' : S} {events : List HostEvent}
    (run : Iterations next n s events s') :
    ∃ count, StepsHN count (decode s) events (decode s') ∧ n / (bound + 1) ≤ count := by
  have localStep : ∀ s events s', next s events s' →
      ∃ count, StepsHN count (decode s) events (decode s') ∧
        1 + potential s' ≤ potential s + (bound + 1) * count := by
    intro s events s' hs
    rcases step s events s' hs with ⟨heq, rfl, hp⟩ | ⟨count, hn, hc⟩
    · refine ⟨0, ?_, by omega⟩
      rw [← heq]
      exact .refl (hw s)
    · refine ⟨count, hc, ?_⟩
      have hmul : bound + 1 ≤ (bound + 1) * count := Nat.le_mul_of_pos_right _ hn
      have := hb s'
      omega
  obtain ⟨count, hc, hp⟩ := iterations_simulation decode potential (bound + 1) hw localStep run
  refine ⟨count, hc, ?_⟩
  have := hb s
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  rw [Nat.succ_mul, Nat.mul_comm count]
  omega

end Exec.Spec
