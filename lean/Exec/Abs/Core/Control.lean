import Exec.Abs.Sim.Instruction

namespace Exec.Abs
open SpecExt Exec.Spec

theorem core_if_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (bt : blocktype) (yes no after : List instr) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩ = .next next) : ATyped next := by
  have hf : FrameTyped s {f with code := .IFELSE bt yes no :: after} [] := by
    cases typed.frames with | cons head _ => exact head
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands hf
  cases hop
  obtain ⟨args, conditions, rfl, _, hcond⟩ := resultsTyped_split hoperands
  cases hcond with
  | cons hv hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hv
    have hi : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
    have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
    simp only [astep, hvals, pop_append, hi, advance, AResult.next.injEq] at step
    rw [← step]
    apply active_frame_preservation typed (if_frame_preservation (f := f) ?_) rfl
    simpa only [hvals] using hf

theorem core_if_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (bt : blocktype) (yes no after : List instr) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩ = .next next) :
    NextSim ⟨s,ambient,{f with code := .IFELSE bt yes no :: after} :: rest,[]⟩ next := by
  have hf : FrameTyped s {f with code := .IFELSE bt yes no :: after} [] := by
    cases typed.frames with | cons head _ => exact head
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ tail => exact framesTyped_wf tail
  obtain ⟨hw,hl,hv,hc⟩ := frameTyped_wf hf
  have hafter : Forall wf_instr after := fun i member => hc i (by simp [member])
  have hi : wf_instr (.IFELSE bt yes no) := hc _ (by simp)
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds hf
  cases hop
  obtain ⟨args, conditions, rfl, hargs, hcond⟩ := resultsTyped_split hoperands
  cases hcond with
  | cons hvalue hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
    have hbits : integer .I32 (integerVal .I32 bits) = some bits := integer_accepts .I32 bits hb
    have hvals : f.vals = (first ++ args) ++ [integerVal .I32 bits] := by simpa only [List.append_assoc] using hsplit
    simp only [astep, hvals, pop_append, hbits, advance, AResult.next.injEq] at step
    rw [← step]
    apply NextSim.single
    have result := if_simulation s ambient f rest after (first ++ args) bits bt yes no
      typed.store typed.ambient hw hl (forall_append hfirst (resultsTyped_wf hargs)) hafter hr
      (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi
    simpa only [← hvals] using result

end Exec.Abs
