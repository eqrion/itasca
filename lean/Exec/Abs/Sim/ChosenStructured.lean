import Exec.Abs.Sim.Structured
import Exec.Abs.Sim.NeutralDecode
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_typed_block_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ = .next next) :
    ChoiceStep choices occurrence (decode ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨C, first, args, inputs, outputs, bindings, _, hop, hsplit, hargs, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop with
    | block _ _ _ ins outs hbt hbody hC hi hnew =>
      have hbt' := blockType_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
      have hlen := resultsTyped_length hargs
      have htypes := results_type_of_typed hargs
      have hheight : f.vals.length - inputs.length = first.length := by rw [hsplit, List.length_append, hlen]; omega
      have hbound : inputs.length ≤ f.vals.length := by rw [hsplit, List.length_append, hlen]; omega
      have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
        rw [hheight, hsplit, List.drop_left]
        exact htypes
      have result := block_simulation s ambient f rest after body first args bt inputs outputs
        typed.store typed.ambient hw hl hfirst (resultsTyped_wf hargs)
        (fun i hm => hc i (by simp [hm])) (framesTyped_wf hr) heights hi
        (blockType_spec s f bt _ hbt') hlen
      have hnext : next = ⟨s, ambient,
          { f with code := body, labels := ⟨outputs, outputs, [], first.length, after⟩ :: f.labels } :: rest, []⟩ := by
        simpa [astep, enterLabel, hbt', hbound, htail, hheight, hsplit, hlen, htypes, advance] using step.symm
      rw [hnext]
      apply chosen_neutral_simulation admissible vector occurrence
      · simpa only [← hsplit] using result
      · simp only [List.map_cons,admininstr_instr,neutralActive]

theorem chosen_typed_loop_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ = .next next) :
    ChoiceStep choices occurrence (decode ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩) [] (decode next) := by
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
      apply chosen_neutral_simulation admissible vector occurrence
      · simpa only [← hsplit] using result
      · simp only [List.map_cons,admininstr_instr,neutralActive]

end Exec.Abs
