import SpecExt.Host

namespace Exec.Spec
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

/-- Every generated execution is an execution with no host events. -/
theorem steps_to_stepsH {c c' : config} (h : Steps c c') : StepsH c [] c' := by
  induction h with
  | refl _ _ hw => exact .refl hw
  | trans _ _ _ _ _ _ hs _ _ _ _ ih => exact .cons (.step hs) ih

/-- An unlabelled extended step uses only the generated semantics. -/
theorem stepH_nil_to_step {c c' : config} (h : StepH c [] c') : Step c c' := by
  generalize he : ([] : List HostEvent) = es at h
  induction h with
  | step h => exact h
  | host_return => cases he
  | host_trap => cases he
  | ctxt_label h h₁ h₂ h₃ h₄ ih => exact .ctxt_label _ _ _ _ _ _ (ih he) h₁ h₂ h₃ h₄
  | ctxt_frame h h₁ h₂ h₃ h₄ ih => exact .ctxt_frame _ _ _ _ _ _ _ _ (ih he) h₁ h₂ h₃ h₄
  | ctxt_instrs h hn h₁ h₂ h₃ h₄ ih => exact .ctxt_instrs _ _ _ _ _ _ (ih he) hn h₁ h₂ h₃ h₄

end Exec.Spec
