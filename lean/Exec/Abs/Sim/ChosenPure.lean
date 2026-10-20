import Exec.Abs.Sim.ChosenContext
import Exec.Spec.Choices.ChosenPure
namespace Exec.Abs
open SpecExt Exec.Spec
theorem chosen_pure_stack {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : Forall wf_val consumed) (hp : Forall wf_val produced)
    (hi : wf_instr instruction)
    (h : ChosenPure choices occurrence (vals consumed ++ [admininstr_instr instruction]) (vals produced)) :
    ChoiceStep choices occurrence (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hb)
      (by intro ai hai; simp only [List.mem_singleton] at hai; subst ai; exact wf_admininstr_instr hi))
  have hw' := wf_config_vals hs hf hp
  have step : ChoiceStep choices occurrence ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced⟩ := h.step admissible s f.toFrame hs hf (wf_config_parts hw).2
  have h₁ := choice_step_instrs admissible step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := choice_decodeLabels admissible h₁ f.labels baseValues hl hv
  have h₃ := choice_active admissible ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

end Exec.Abs
