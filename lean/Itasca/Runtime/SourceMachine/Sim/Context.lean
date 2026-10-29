import Itasca.Runtime.SourceMachine.Step
import Itasca.Runtime.Spec.Context

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Syntactic well-formedness of the suspended continuations. -/
def LabelsWf (labels : List Label) : Prop :=
  Forall (fun label => Forall wf_instr label.cont ∧ Forall wf_instr label.after) labels

private theorem forall_take {α : Type} {P : α → Prop} {xs : List α}
    (h : Forall P xs) (n : Nat) : Forall P (xs.take n) := by
  intro x hx
  exact h x (List.mem_of_mem_take hx)

private theorem forall_drop {α : Type} {P : α → Prop} {xs : List α}
    (h : Forall P xs) (n : Nat) : Forall P (xs.drop n) := by
  intro x hx
  exact h x (List.mem_of_mem_drop hx)

/-- Lift a redex through the entire explicit label stack. -/
theorem step_h_decode_labels {z z' : state} {code code' : List admininstr}
    {events : List HostEvent} (h : StepH ⟨z, code⟩ events ⟨z', code'⟩)
    (labels : List Label) (values : List val)
    (hl : LabelsWf labels) (hv : Forall wf_val values) :
    StepH ⟨z, decodeLabels labels values code⟩ events
      ⟨z', decodeLabels labels values code'⟩ := by
  induction labels generalizing values code code' with
  | nil =>
    simpa [instrContext, decodeLabels] using step_h_instrs h values [] hv (forall_nil _)
  | cons label labels ih =>
    have hc := (hl label (by simp)).1
    have ha := (hl label (by simp)).2
    have hr : LabelsWf labels := fun x hx => hl x (by simp [hx])
    have h₁ := step_h_instrs h (values.drop label.height) []
      (forall_drop hv _) (forall_nil _)
    have h₂ := step_h_label h₁ label.arity label.cont hc
    have h₃ := step_h_instrs h₂ [] (label.after.map admininstr_instr)
      (forall_nil _) (wf_instrs ha)
    have h₄ := ih h₃ (values.take label.height) hr (forall_take hv _)
    simpa [decodeLabels, instrContext, labelContext, vals] using h₄

/-- Moving values from code into the flat stack changes no decoded instructions,
provided the moved values remain above the innermost label's saved height. -/
theorem decode_labels_move_values (labels : List Label) (values extra : List val)
    (code : List admininstr)
    (heights : ∀ label ∈ labels, label.height ≤ values.length) :
    decodeLabels labels (values ++ extra) code =
      decodeLabels labels values (vals extra ++ code) := by
  cases labels with
  | nil => simp [decodeLabels, vals, List.map_append, List.append_assoc]
  | cons label labels =>
    have h := heights label (by simp)
    simp only [decodeLabels, List.take_append_of_le_length h,
      List.drop_append_of_le_length h, vals, List.map_append, List.append_assoc]

/-- Syntactic requirements for suspended callers, separate from semantic typing. -/
def FrameWf (f : AFrame) : Prop :=
  wf_frame f.toFrame ∧ LabelsWf f.labels ∧ Forall wf_val f.vals ∧ Forall wf_instr f.code

def activeFrame (ambient : frame) : List AFrame → frame
  | [] => ambient
  | f :: _ => f.toFrame

theorem active_frame_wf {ambient : frame} {frames : List AFrame}
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    wf_frame (activeFrame ambient frames) := by
  cases frames with
  | nil => exact ha
  | cons f rest => exact (hf f (by simp)).1

/-- Lift through all suspended callers, each in its own local/module context. -/
theorem step_h_decode_frames {s s' : store} (ambient : frame) (frames : List AFrame)
    {code code' : List admininstr} {events : List HostEvent}
    (h : StepH ⟨⟨s, activeFrame ambient frames⟩, code⟩ events
      ⟨⟨s', activeFrame ambient frames⟩, code'⟩)
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    StepH ⟨⟨s, ambient⟩, decodeFrames frames code⟩ events
      ⟨⟨s', ambient⟩, decodeFrames frames code'⟩ := by
  induction frames generalizing code code' with
  | nil => exact h
  | cons f rest ih =>
    obtain ⟨_, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun x hx => hf x (by simp [hx])
    have h₁ := step_h_instrs h [] (f.code.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)
    have h₂ := step_h_decode_labels h₁ f.labels f.vals hl hv
    have h₃ := step_h_frame h₂ f.arity (activeFrame ambient rest) (active_frame_wf ha hr)
    have h₄ := ih h₃ hr
    simpa [decodeFrames, activeFrame, instrContext, frameContext, vals] using h₄

/-- Lift a transition in the current frame through its frame boundary and callers.
The inner frame may change locals, while its result arity stays fixed. -/
theorem step_h_active {s s' : store} (ambient : frame) (rest : List AFrame)
    (arity : Nat) {inner inner' : frame} {body body' : List admininstr}
    {events : List HostEvent}
    (h : StepH ⟨⟨s, inner⟩, body⟩ events ⟨⟨s', inner'⟩, body'⟩)
    (ha : wf_frame ambient) (hr : Forall FrameWf rest) :
    StepH ⟨⟨s, ambient⟩, decodeFrames rest [.FRAME_ arity inner body]⟩ events
      ⟨⟨s', ambient⟩, decodeFrames rest [.FRAME_ arity inner' body']⟩ := by
  exact step_h_decode_frames ambient rest
    (step_h_frame h arity (activeFrame ambient rest) (active_frame_wf ha hr)) ha hr

end Itasca.Runtime.SourceMachine
