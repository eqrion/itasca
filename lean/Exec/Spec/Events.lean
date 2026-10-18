import Exec.Spec.Steps

namespace Exec.Spec
open SpecExt

/-- A single reduction can record at most one direct host call. -/
theorem stepH_event_length {c c' : config} {es : List HostEvent}
    (h : StepH c es c') : es.length ≤ 1 := by
  induction h <;> simp_all

/-- Every recorded event originates in a host reduction, even under contexts. -/
theorem stepH_event_host {c c' : config} {es : List HostEvent}
    (h : StepH c es c') {event : HostEvent} (he : event ∈ es) :
    ∃ s fa id params results args out,
      event = .call fa args out ∧ HostFunction s fa id params results ∧
      ResultsTyped s params args := by
  induction h with
  | step => simp at he
  | host_return hh ha =>
    simp only [List.mem_singleton] at he
    subst event
    exact ⟨_, _, _, _, _, _, _, rfl, hh, ha⟩
  | host_trap hh ha =>
    simp only [List.mem_singleton] at he
    subst event
    exact ⟨_, _, _, _, _, _, _, rfl, hh, ha⟩
  | ctxt_label _ _ _ _ _ ih => exact ih he
  | ctxt_frame _ _ _ _ _ ih => exact ih he
  | ctxt_instrs _ _ _ _ _ _ ih => exact ih he

/-- Empty-event executions introduce no additional non-host behavior. -/
theorem stepsH_nil_to_steps {c c' : config} (h : StepsH c [] c') : Steps c c' := by
  generalize he : ([] : List HostEvent) = es at h
  induction h with
  | @refl c hw =>
    cases c with | mk_config z body => exact .refl z body hw
  | @cons c c' c'' events rest hs hr ih =>
    have hnil : events = [] ∧ rest = [] := List.append_eq_nil_iff.mp he.symm
    rcases hnil with ⟨rfl, rfl⟩
    have hw := stepH_wf hs
    have hw' := stepsH_wf hr
    cases c with | mk_config z body =>
      cases c' with | mk_config z' body' =>
        cases c'' with | mk_config z'' body'' =>
          exact .trans _ _ _ _ _ _ (stepH_nil_to_step hs) (ih rfl) hw.1 hw'.2 hw.2

end Exec.Spec
