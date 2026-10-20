import Exec.Abs.Sim.Basic
import Exec.Spec.Choices.ChosenContext
/-! A fixed source policy lifts through actual abstract label stacks, callers,
and operand prefixes without consuming additional source occurrences. -/
namespace Exec.Abs
open SpecExt Exec.Spec

private theorem chosen_forall_take {A : Type} {P : A → Prop} {values : List A}
    (all : Forall P values) (count : Nat) : Forall P (values.take count) := by
  intro value member
  exact all value (List.mem_of_mem_take member)

private theorem chosen_forall_drop {A : Type} {P : A → Prop} {values : List A}
    (all : Forall P values) (count : Nat) : Forall P (values.drop count) := by
  intro value member
  exact all value (List.mem_of_mem_drop member)

theorem choice_decodeLabels {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} {z z' : state} {code code' : List admininstr}
    {events : List HostEvent} (h : ChoiceStep choices occurrence ⟨z, code⟩ events ⟨z', code'⟩)
    (labels : List Label) (values : List val)
    (hl : LabelsWf labels) (hv : Forall wf_val values) :
    ChoiceStep choices occurrence ⟨z, decodeLabels labels values code⟩ events
      ⟨z', decodeLabels labels values code'⟩ := by
  induction labels generalizing values code code' with
  | nil =>
    simpa [instrContext, decodeLabels] using choice_step_instrs admissible h values [] hv (forall_nil _)
  | cons label labels ih =>
    have hc := (hl label (by simp)).1
    have ha := (hl label (by simp)).2
    have hr : LabelsWf labels := fun x hx => hl x (by simp [hx])
    have h₁ := choice_step_instrs admissible h (values.drop label.height) []
      (chosen_forall_drop hv _) (forall_nil _)
    have h₂ := choice_step_label admissible h₁ label.arity label.cont hc
    have h₃ := choice_step_instrs admissible h₂ [] (label.after.map admininstr_instr)
      (forall_nil _) (wf_instrs ha)
    have h₄ := ih h₃ (values.take label.height) hr (chosen_forall_take hv _)
    simpa [decodeLabels, instrContext, labelContext, vals] using h₄

theorem choice_decodeFrames {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} {s s' : store} (ambient : frame) (frames : List AFrame)
    {code code' : List admininstr} {events : List HostEvent}
    (h : ChoiceStep choices occurrence ⟨⟨s, activeFrame ambient frames⟩, code⟩ events
      ⟨⟨s', activeFrame ambient frames⟩, code'⟩)
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    ChoiceStep choices occurrence ⟨⟨s, ambient⟩, decodeFrames frames code⟩ events
      ⟨⟨s', ambient⟩, decodeFrames frames code'⟩ := by
  induction frames generalizing code code' with
  | nil => exact h
  | cons f rest ih =>
    obtain ⟨_, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun x hx => hf x (by simp [hx])
    have h₁ := choice_step_instrs admissible h [] (f.code.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)
    have h₂ := choice_decodeLabels admissible h₁ f.labels f.vals hl hv
    have h₃ := choice_step_frame admissible h₂ f.arity (activeFrame ambient rest) (activeFrame_wf ha hr)
    have h₄ := ih h₃ hr
    simpa [decodeFrames, activeFrame, instrContext, frameContext, vals] using h₄

/-- Lift a transition in the current frame through its frame boundary and callers.
The inner frame may change locals, while its result arity stays fixed. -/
theorem choice_active {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} {s s' : store} (ambient : frame) (rest : List AFrame)
    (arity : Nat) {inner inner' : frame} {body body' : List admininstr}
    {events : List HostEvent}
    (h : ChoiceStep choices occurrence ⟨⟨s, inner⟩, body⟩ events ⟨⟨s', inner'⟩, body'⟩)
    (ha : wf_frame ambient) (hr : Forall FrameWf rest) :
    ChoiceStep choices occurrence ⟨⟨s, ambient⟩, decodeFrames rest [.FRAME_ arity inner body]⟩ events
      ⟨⟨s', ambient⟩, decodeFrames rest [.FRAME_ arity inner' body']⟩ := by
  exact choice_decodeFrames admissible ambient rest
    (choice_step_frame admissible h arity (activeFrame ambient rest) (activeFrame_wf ha hr)) ha hr

theorem choice_stack_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (ha : wf_frame ambient)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : ChoiceStep choices occurrence ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced⟩) :
    ChoiceStep choices occurrence (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have h₁ := choice_step_instrs admissible step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := choice_decodeLabels admissible h₁ f.labels baseValues hl hv
  have h₃ := choice_active admissible ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

end Exec.Abs
