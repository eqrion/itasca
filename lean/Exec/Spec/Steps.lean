import SpecExt.Host

namespace Itasca.Runtime.Spec
open SpecExt

/-- Endpoint well-formedness follows directly from generated constructors.
This proof deliberately does not use the unfinished Step_is_wf theorem. -/
theorem step_wf {c c' : config} (h : Step c c') : wf_config c ∧ wf_config c' := by
  cases h <;> exact ⟨by assumption, by assumption⟩

theorem stepH_wf {c c' : config} {es : List HostEvent}
    (h : StepH c es c') : wf_config c ∧ wf_config c' := by
  cases h with
  | step h => exact step_wf h
  | _ => exact ⟨by assumption, by assumption⟩

theorem stepsH_wf {c c' : config} {es : List HostEvent}
    (h : StepsH c es c') : wf_config c ∧ wf_config c' := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | cons h _ ih => exact ⟨(stepH_wf h).1, ih.2⟩

theorem stepsH_single {c c' : config} {es : List HostEvent}
    (h : StepH c es c') : StepsH c es c' := by
  simpa using StepsH.cons h (StepsH.refl (stepH_wf h).2)

theorem stepsH_trans {c c' c'' : config} {es rest : List HostEvent}
    (h : StepsH c es c') (h' : StepsH c' rest c'') :
    StepsH c (es ++ rest) c'' := by
  induction h with
  | refl _ => simpa using h'
  | cons h _ ih => simpa [List.append_assoc] using StepsH.cons h (ih h')

end Itasca.Runtime.Spec
