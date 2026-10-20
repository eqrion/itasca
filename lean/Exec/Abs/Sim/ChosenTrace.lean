import Exec.Abs.Sim.ChosenContext
import Exec.Spec.Counted

namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosenStepsN_label {choices : SourceChoices} (admissible : choices.Admissible) {occurrence n : Nat} {c c' : config} {events : List HostEvent}
    (h : ChosenStepsN choices occurrence n c events c') (arity : Nat) (cont : List instr) (hc : Forall wf_instr cont) :
    ChosenStepsN choices occurrence n (Exec.Spec.labelContext arity cont c) events (Exec.Spec.labelContext arity cont c') := by
  apply ChosenStepsN.map ?_ (fun _ _ _ _ h => choice_step_label admissible h arity cont hc)
  · exact h
  intro c hw
  cases c
  exact wf_config_label arity hw hc

theorem chosenStepsN_frame {choices : SourceChoices} (admissible : choices.Admissible) {occurrence n : Nat} {c c' : config} {events : List HostEvent}
    (h : ChosenStepsN choices occurrence n c events c') (arity : Nat) (outer : frame) (hf : wf_frame outer) :
    ChosenStepsN choices occurrence n (frameContext arity outer c) events (frameContext arity outer c') := by
  apply ChosenStepsN.map ?_ (fun _ _ _ _ h => choice_step_frame admissible h arity outer hf)
  · exact h
  intro c hw
  cases c with | mk_config z code =>
    cases z
    exact wf_config_frame arity hw hf

theorem chosenStepsN_instrs {choices : SourceChoices} (admissible : choices.Admissible) {occurrence n : Nat} {c c' : config} {events : List HostEvent}
    (h : ChosenStepsN choices occurrence n c events c') (values : List val) (after : List admininstr)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    ChosenStepsN choices occurrence n (instrContext values after c) events (instrContext values after c') := by
  apply ChosenStepsN.map ?_ (fun _ _ _ _ h => choice_step_instrs admissible h values after hv ha)
  · exact h
  intro c hw
  cases c
  exact wf_config_instrs hw hv ha

theorem chosenStepsN_decodeLabels {choices : SourceChoices} (admissible : choices.Admissible) {occurrence n : Nat} {z z' : state} {code code' : List admininstr}
    {events : List HostEvent} (h : ChosenStepsN choices occurrence n ⟨z, code⟩ events ⟨z', code'⟩)
    (labels : List Label) (values : List val)
    (hl : LabelsWf labels) (hv : Forall wf_val values) :
    ChosenStepsN choices occurrence n ⟨z, decodeLabels labels values code⟩ events
      ⟨z', decodeLabels labels values code'⟩ := by
  induction labels generalizing values code code' with
  | nil => simpa [instrContext, decodeLabels] using chosenStepsN_instrs admissible h values [] hv (forall_nil _)
  | cons label labels ih =>
    have h₁ := chosenStepsN_instrs admissible h (values.drop label.height) []
      (fun v hm => hv v (List.mem_of_mem_drop hm)) (forall_nil _)
    have h₂ := chosenStepsN_label admissible h₁ label.arity label.cont (hl label (by simp)).1
    have h₃ := chosenStepsN_instrs admissible h₂ [] (label.after.map admininstr_instr)
      (forall_nil _) (wf_instrs (hl label (by simp)).2)
    have h₄ := ih h₃ (values.take label.height) (fun l hm => hl l (by simp [hm]))
      (fun v hm => hv v (List.mem_of_mem_take hm))
    simpa [decodeLabels, instrContext, Exec.Spec.labelContext, vals] using h₄

theorem chosenStepsN_decodeFrames {choices : SourceChoices} (admissible : choices.Admissible) {occurrence n : Nat} {s s' : store} (ambient : frame) (frames : List AFrame)
    {code code' : List admininstr} {events : List HostEvent}
    (h : ChosenStepsN choices occurrence n ⟨⟨s, activeFrame ambient frames⟩, code⟩ events
      ⟨⟨s', activeFrame ambient frames⟩, code'⟩)
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    ChosenStepsN choices occurrence n ⟨⟨s, ambient⟩, decodeFrames frames code⟩ events
      ⟨⟨s', ambient⟩, decodeFrames frames code'⟩ := by
  induction frames generalizing code code' with
  | nil => exact h
  | cons f rest ih =>
    obtain ⟨_, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun x hx => hf x (by simp [hx])
    have h₁ := chosenStepsN_instrs admissible h [] (f.code.map admininstr_instr) (forall_nil _) (wf_instrs hc)
    have h₂ := chosenStepsN_decodeLabels admissible h₁ f.labels f.vals hl hv
    have h₃ := chosenStepsN_frame admissible h₂ f.arity (activeFrame ambient rest) (activeFrame_wf ha hr)
    have h₄ := ih h₃ hr
    simpa [decodeFrames, activeFrame, instrContext, frameContext, vals] using h₄

end Exec.Abs
