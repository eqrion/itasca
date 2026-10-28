import Itasca.Runtime.Abs.Sim.Instruction
import Itasca.Runtime.Abs.Core.Step
namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem typed_loop_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ = .next next) :
    StepH (decode ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨C, first, args, inputs, outputs, bindings, _, hop, hsplit, hargs, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop with
    | loop _ _ _ ins outs hbt hbody hC hi hnew =>
      have hbt' := blockType_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
      have hlen := resultsTyped_length hargs
      have htypes := results_type_of_typed hargs
      have hheight : f.vals.length - inputs.length = first.length := by rw [hsplit, List.length_append, hlen]; omega
      have hbound : inputs.length ≤ f.vals.length := by rw [hsplit, List.length_append, hlen]; omega
      have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
        rw [hheight, hsplit, List.drop_left]
        exact htypes
      have result := loop_simulation s ambient f rest after body first args bt inputs outputs
        typed.store typed.ambient hw hl hfirst (resultsTyped_wf hargs)
        (fun i hm => hc i (by simp [hm])) (framesTyped_wf hr) heights hi
        (blockType_spec s f bt _ hbt') hlen
      have hnext : next = ⟨s, ambient,
          { f with code := body, labels := ⟨inputs, outputs, [.LOOP bt body], first.length, after⟩ :: f.labels } :: rest, []⟩ := by
        simpa [astep, enterLabel, hbt', hbound, htail, hheight, hsplit, hlen, htypes, advance] using step.symm
      rw [hnext]
      simpa only [← hsplit] using result

theorem typed_if_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (yes no : List instr) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩) [] (decode next) := by
  have hf : FrameTyped s { f with code := .IFELSE bt yes no :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact framesTyped_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
  have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
  have hi : wf_instr (.IFELSE bt yes no) := hc (.IFELSE bt yes no) (by simp)
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
    have result := if_simulation s ambient f rest after (first ++ args) bits bt yes no
      typed.store typed.ambient hw hl (forall_append hfirst (resultsTyped_wf hargs)) hafter hr
      (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi
    simpa only [← hvals] using result

theorem typed_br_if_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (depth : Nat) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩)
    (step : astep ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩) [] (decode next) := by
  have hf : FrameTyped s { f with code := .BR_IF (.mk_uN depth) :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact framesTyped_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
  have hafter : Forall wf_instr after := fun i hm => hc i (by simp [hm])
  have hi : wf_instr (.BR_IF (.mk_uN depth)) := hc (.BR_IF (.mk_uN depth)) (by simp)
  have hi32 : depth < 2 ^ 32 := by
    cases hi with
    | instr_case_8 _ hu => cases hu with
      | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
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
    have result := br_if_simulation s ambient f rest after (first ++ args) bits depth
      typed.store typed.ambient hw hl (forall_append hfirst (resultsTyped_wf hargs)) hafter hr
      (by intro label hm; have hh := heights label hm; simp only [List.length_append]; omega) hb hi32
    simpa only [← hvals] using result

end Itasca.Runtime.Abs
