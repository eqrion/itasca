import Exec.Abs.Core.Simulation
import Exec.Abs.Sim.ChosenTrap
import Exec.Abs.Sim.NeutralDecode

namespace Exec.Abs
open SpecExt Exec.Spec

/-- An instruction-local bounds or arithmetic trap unwinds all labels and
callers after consuming exactly the typed redex operands. -/
theorem chosen_operand_trap_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (front consumed : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (step : StepH ⟨⟨s,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s,f.toFrame⟩,[.TRAP]⟩)
    (neutral : neutralActive (vals consumed ++ [admininstr_instr instruction])=true) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s,ambient,{f with code := instruction :: after, vals := front ++ consumed} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have selected := stepH_neutral_chosen admissible vector occurrence step neutral
  have lifted := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible (choice_step_instrs admissible selected [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels front hl hv) ha hr
  have framesWf : Forall FrameWf ({f with code := after, vals := front} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := chosen_trap_frames choices (occurrence+1) s ambient ({f with code := after, vals := front} :: rest) hs ha framesWf
  refine ⟨n+1,by omega,?_⟩
  have combined := ChosenStepsN.cons lifted tail
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeFrames,frameContext,instrContext,vals,List.append_assoc,AFrame.toFrame,AFrame.arity] using combined

end Exec.Abs
