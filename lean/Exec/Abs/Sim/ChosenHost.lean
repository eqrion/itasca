import Exec.Abs.Sim.Call
import Exec.Abs.Sim.ChosenTrap
import Exec.Spec.Choices.NeutralStep
namespace Exec.Abs
open SpecExt Exec.Spec

/-- A direct host call resolves its module index and then returns atomically.
The host event and changed store survive all labels and suspended callers. -/
theorem host_return_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (baseValues args results : List val) (events : List HostEvent)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (hargs : Forall wf_val args)
    (host : ChoiceStep choices (occurrence+1) ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,vals results⟩) :
    ChosenStepsN choices occurrence 2
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after,vals := baseValues ++ args} :: rest,[]⟩)
      events
      (decode ⟨s',ambient,{f with code := after,vals := baseValues ++ results} :: rest,[]⟩) := by
  have resolveChoice := stepH_neutral_chosen admissible vector occurrence (call_resolve s f.toFrame index address hs hf resolve hi32) (by simp only [trapCode,neutralActive])
  have first := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible
      (choice_step_instrs admissible resolveChoice
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible (choice_step_instrs admissible host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := ChosenStepsN.cons first (ChosenStepsN.cons second (ChosenStepsN.refl _ (second.wf admissible).2))
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights,decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr] using both

/-- Host traps retain callback store effects while the source semantics unwinds
all remaining labels and callers. Unwinding emits no additional host events. -/
theorem host_trap_chosen_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s s' : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat)
    (baseValues args : List val) (events : List HostEvent)
    (hs : wf_store s) (hs' : wf_store s') (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (hargs : Forall wf_val args)
    (host : ChoiceStep choices (occurrence+1) ⟨⟨s,f.toFrame⟩,vals args ++ [.CALL_ADDR address]⟩ events
      ⟨⟨s',f.toFrame⟩,[.TRAP]⟩) :
    ∃ n, 2 ≤ n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s,ambient,{f with code := .CALL (.mk_uN index) :: after,vals := baseValues ++ args} :: rest,[]⟩)
      events ⟨⟨s',ambient⟩,[.TRAP]⟩ := by
  have resolveChoice := stepH_neutral_chosen admissible vector occurrence (call_resolve s f.toFrame index address hs hf resolve hi32) (by simp only [trapCode,neutralActive])
  have first := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible
      (choice_step_instrs admissible resolveChoice
        args (after.map admininstr_instr) hargs (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have second := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible (choice_step_instrs admissible host [] (after.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)) f.labels baseValues hl hv) ha hr
  have frames : Forall FrameWf ({f with vals := baseValues,code := after} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := chosen_trap_frames choices (occurrence+2) s' ambient ({f with vals := baseValues,code := after} :: rest) hs' ha frames
  have tail' : ChosenStepsN choices (occurrence+2) n _ [] ⟨⟨s',ambient⟩,[.TRAP]⟩ := tail
  simp only [vals,List.map_nil,List.nil_append,List.append_assoc] at first second
  have both := ChosenStepsN.cons first (ChosenStepsN.cons second tail')
  refine ⟨n+2,by omega,?_⟩
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeFrames,instrContext,vals,List.append_assoc,AFrame.arity,AFrame.toFrame,admininstr_instr,Nat.add_assoc] using both
end Exec.Abs
