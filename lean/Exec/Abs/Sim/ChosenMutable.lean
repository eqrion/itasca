import Exec.Abs.Sim.ChosenContext
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_mutable_stack_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (ha : wf_frame ambient)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : ChoiceStep choices occurrence ⟨⟨before, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore, f.toFrame⟩, vals produced⟩) :
    ChoiceStep choices occurrence (decode ⟨before, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨afterStore, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have h₁ := choice_step_instrs admissible step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := choice_decodeLabels admissible h₁ f.labels baseValues hl hv
  have h₃ := choice_active admissible ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

end Exec.Abs
