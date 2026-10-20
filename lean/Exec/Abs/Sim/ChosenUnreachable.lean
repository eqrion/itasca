import Exec.Abs.Sim.Trap
import Exec.Abs.Sim.ChosenContext
import Exec.Abs.Sim.ChosenTrap
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_unreachable_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, [.UNREACHABLE]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_1)
  have ht := wf_config_make hs hf wf_trap
  have step : ChoiceStep choices occurrence ⟨⟨s, f.toFrame⟩, [.UNREACHABLE]⟩ [] ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    .ordinary_pure (.unreachable .admininstr_case_1 .admininstr_case_73) rfl hw ht
  have lifted := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible (choice_step_instrs admissible step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels f.vals hl hv) ha hr
  have hframes : Forall FrameWf ({ f with code := after } :: rest) := by
    intro frame hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hf, hl, hv, hc⟩
    · exact hr frame hm
  obtain ⟨n, tail⟩ := chosen_trap_frames choices (occurrence+1) s ambient ({ f with code := after } :: rest) hs ha hframes
  refine ⟨n + 1, by omega, ?_⟩
  simpa [decode, decodeFrames, vals, instrContext, AFrame.arity, AFrame.toFrame, admininstr_instr] using
    ChosenStepsN.cons lifted tail

end Exec.Abs
