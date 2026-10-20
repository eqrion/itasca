import Exec.Abs.Float.Simulation
import Exec.Abs.Sim.ChosenPure
import Exec.Abs.Sim.ChosenTrap
namespace Exec.Abs.Float
open SpecExt Exec.Spec

/-- Scalar outcomes with a fixed active-reply witness, rather than only
membership in the source's nondeterministic reduction relation. -/
def Instruction.ChosenResult (op : Instruction) (choices : SourceChoices) (occurrence : Nat)
    (a b : Nat) (result : Option Nat) : Prop :=
  match result with
  | some bits => bits<2^sizenn op.output ∧
      ChosenPure choices occurrence (vals (op.operands a b)++[admininstr_instr op.source])
        [admininstr_val (.CONST op.output (numberOfBits op.output bits))]
  | none => ChosenPure choices occurrence (vals (op.operands a b)++[admininstr_instr op.source]) [.TRAP]

theorem Instruction.ChosenResult.erases {op : Instruction} {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence a b : Nat} {result : Option Nat} (source : op.ChosenResult choices occurrence a b result) : op.Result a b result := by
  cases result with
  | none => exact ChosenPure.erases admissible source
  | some bits => exact ⟨source.1,ChosenPure.erases admissible source.2⟩

theorem Instruction.chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b bits : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (effect : op.ChosenResult choices occurrence a b (some bits))
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    ChoiceStep choices occurrence (decode ⟨s, ambient,
      { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } :: rest, []⟩) := by
  apply chosen_pure_stack admissible s ambient f rest _ after front _ _ hs ha hf hl hv hc hr heights
  · exact op.operands_wf a b first second
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact .val_case_0 _ _ (numberOfBits_wf _ _ effect.1)
  · exact op.source_wf
  · exact effect.2


theorem Instruction.chosen_trap_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (op : Instruction) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (trap : op.ChosenResult choices occurrence a b none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s, ambient,
        { f with code := op.source :: after, vals := baseValues ++ op.operands a b } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  let operands := op.operands a b
  have operandsWf : Forall wf_val operands := op.operands_wf a b first second
  have instructionWf : wf_instr op.source := op.source_wf
  have before : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [admininstr_instr op.source]⟩ := wf_config_make hs hf (forall_append (wf_vals operandsWf)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr instructionWf))
  have step : ChoiceStep choices occurrence ⟨⟨s, f.toFrame⟩, vals operands ++
      [admininstr_instr op.source]⟩ [] ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    ChosenPure.step admissible trap s f.toFrame hs hf (wf_config_parts before).2
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

end Exec.Abs.Float
