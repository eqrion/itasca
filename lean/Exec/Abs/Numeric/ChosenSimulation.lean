import Exec.Abs.Numeric.ChosenInstruction
import Exec.Abs.Sim.ChosenPure
import Exec.Abs.Sim.ChosenTrap
namespace Exec.Abs.Numeric
open SpecExt Exec.Spec

theorem Instruction.chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    ChoiceStep choices occurrence (decode ⟨s, ambient,
      { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := front ++ [integerVal op.output result.toNat] } :: rest, []⟩) := by
  apply chosen_pure_stack admissible s ambient f rest _ after front _ _ hs ha hf hl hv hc hr heights
  · exact op.operands_wf a b
  · intro value h; simp only [List.mem_singleton] at h; subst value
    exact integer_val_wf _ _ (word_bound _ _)
  · exact op.source_wf
  · exact op.chosen_pure_success admissible occurrence a b result success

theorem Instruction.chosen_trap_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (op : Instruction) (a b : BitVec (sizenn (numtype_Inn op.input)))
    (trap : op.apply a b = none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s, ambient,
        { f with code := op.source :: after, vals := baseValues ++ op.operands a b } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  let operands := op.operands a b
  have operandsWf : Forall wf_val operands := op.operands_wf a b
  have instructionWf : wf_instr op.source := op.source_wf
  have before : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [admininstr_instr op.source]⟩ := wf_config_make hs hf (forall_append (wf_vals operandsWf)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr instructionWf))
  have step : ChoiceStep choices occurrence ⟨⟨s, f.toFrame⟩, vals operands ++
      [admininstr_instr op.source]⟩ [] ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    ChosenPure.step admissible (op.chosen_pure_trap admissible occurrence a b trap) s f.toFrame hs hf (wf_config_parts before).2
  have lifted := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible (choice_step_instrs admissible step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels baseValues hl hv) ha hr
  have frameWf : Forall FrameWf ({ f with code := after, vals := baseValues } :: rest) := by
    intro frame hm; simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hf, hl, hv, hc⟩
    · exact hr frame hm
  obtain ⟨n, tail⟩ := chosen_trap_frames choices (occurrence+1) s ambient ({ f with code := after, vals := baseValues } :: rest) hs ha frameWf
  refine ⟨n + 1, by omega, ?_⟩
  have all := ChosenStepsN.cons lifted tail
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeFrames, operands, vals, instrContext, AFrame.toFrame, AFrame.arity, List.append_assoc] using all

end Exec.Abs.Numeric
