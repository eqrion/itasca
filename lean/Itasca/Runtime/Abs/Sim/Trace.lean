import Itasca.Runtime.Abs.Sim.Typing
import Itasca.Runtime.Spec.Counted

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem stepsHN_label {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') (arity : Nat) (cont : List instr) (hc : Forall wf_instr cont) :
    StepsHN n (Itasca.Runtime.Spec.labelContext arity cont c) events (Itasca.Runtime.Spec.labelContext arity cont c') := by
  apply h.map ?_ (fun _ _ _ h => stepH_label h arity cont hc)
  intro c hw
  cases c
  exact wf_config_label arity hw hc

theorem stepsHN_frame {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') (arity : Nat) (outer : frame) (hf : wf_frame outer) :
    StepsHN n (frameContext arity outer c) events (frameContext arity outer c') := by
  apply h.map ?_ (fun _ _ _ h => stepH_frame h arity outer hf)
  intro c hw
  cases c with | mk_config z code =>
    cases z
    exact wf_config_frame arity hw hf

theorem stepsHN_instrs {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') (values : List val) (after : List admininstr)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    StepsHN n (instrContext values after c) events (instrContext values after c') := by
  apply h.map ?_ (fun _ _ _ h => stepH_instrs h values after hv ha)
  intro c hw
  cases c
  exact wf_config_instrs hw hv ha

theorem stepsHN_decodeLabels {n : Nat} {z z' : state} {code code' : List admininstr}
    {events : List HostEvent} (h : StepsHN n ⟨z, code⟩ events ⟨z', code'⟩)
    (labels : List Label) (values : List val)
    (hl : LabelsWf labels) (hv : Forall wf_val values) :
    StepsHN n ⟨z, decodeLabels labels values code⟩ events
      ⟨z', decodeLabels labels values code'⟩ := by
  induction labels generalizing values code code' with
  | nil => simpa [instrContext, decodeLabels] using stepsHN_instrs h values [] hv (forall_nil _)
  | cons label labels ih =>
    have h₁ := stepsHN_instrs h (values.drop label.height) []
      (fun v hm => hv v (List.mem_of_mem_drop hm)) (forall_nil _)
    have h₂ := stepsHN_label h₁ label.arity label.cont (hl label (by simp)).1
    have h₃ := stepsHN_instrs h₂ [] (label.after.map admininstr_instr)
      (forall_nil _) (wf_instrs (hl label (by simp)).2)
    have h₄ := ih h₃ (values.take label.height) (fun l hm => hl l (by simp [hm]))
      (fun v hm => hv v (List.mem_of_mem_take hm))
    simpa [decodeLabels, instrContext, Itasca.Runtime.Spec.labelContext, vals] using h₄

theorem stepsHN_decodeFrames {n : Nat} {s s' : store} (ambient : frame) (frames : List AFrame)
    {code code' : List admininstr} {events : List HostEvent}
    (h : StepsHN n ⟨⟨s, activeFrame ambient frames⟩, code⟩ events
      ⟨⟨s', activeFrame ambient frames⟩, code'⟩)
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    StepsHN n ⟨⟨s, ambient⟩, decodeFrames frames code⟩ events
      ⟨⟨s', ambient⟩, decodeFrames frames code'⟩ := by
  induction frames generalizing code code' with
  | nil => exact h
  | cons f rest ih =>
    obtain ⟨_, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun x hx => hf x (by simp [hx])
    have h₁ := stepsHN_instrs h [] (f.code.map admininstr_instr) (forall_nil _) (wf_instrs hc)
    have h₂ := stepsHN_decodeLabels h₁ f.labels f.vals hl hv
    have h₃ := stepsHN_frame h₂ f.arity (activeFrame ambient rest) (activeFrame_wf ha hr)
    have h₄ := ih h₃ hr
    simpa [decodeFrames, activeFrame, instrContext, frameContext, vals] using h₄

end Itasca.Runtime.Abs
