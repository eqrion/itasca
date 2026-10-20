import Exec.Abs.Sim.Return
import Exec.Abs.Sim.NeutralDecode
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_return_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (labels : List Label) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (nested : LabelsNested labels) (bound : f.arity ≤ f.vals.length)
    (heights : ∀ label ∈ labels, label.height ≤ f.vals.length) :
    ChosenStepsN choices occurrence (labels.length + 1) (decode ⟨s, ambient,
      { f with code := .RETURN :: after, labels := labels } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, decodeFrames rest (vals (f.vals.drop (f.vals.length - f.arity)))⟩ := by
  induction labels generalizing after occurrence with
  | nil =>
    have step := return_frame_simulation s ambient f rest after
      (f.vals.take (f.vals.length - f.arity)) (f.vals.drop (f.vals.length - f.arity))
      hs ha hf (fun v hm => hv v (List.mem_of_mem_take hm))
      (fun v hm => hv v (List.mem_of_mem_drop hm)) hc hr
      (by simp only [List.length_drop]; omega)
    have chosen := chosen_neutral_simulation admissible vector occurrence step
      (by simp only [List.map_cons,admininstr_instr,neutralActive])
    simpa only [List.take_append_drop, List.length_nil, List.nil_append] using
      ChosenStepsN.cons chosen (ChosenStepsN.refl (occurrence+1) (chosen.wf admissible).2)
  | cons label labels ih =>
    have hb := heights label (by simp)
    have first := return_label_simulation s ambient f rest label labels after
      (f.vals.take label.height) (f.vals.drop label.height) hs ha hf hl
      (fun v hm => hv v (List.mem_of_mem_take hm))
      (fun v hm => hv v (List.mem_of_mem_drop hm)) hc hr
      (by simp only [List.length_take]; omega)
      (by intro l hm; have hh := nested.1 l hm; simp only [List.length_take]; omega)
    have first' : StepH (decode ⟨s, ambient, { f with code := .RETURN :: after, labels := label :: labels } :: rest, []⟩) []
        (decode ⟨s, ambient, { f with code := .RETURN :: label.after, labels := labels } :: rest, []⟩) := by
      simpa only [List.take_append_drop] using first
    have chosen := chosen_neutral_simulation admissible vector occurrence first'
      (by simp only [List.map_cons,admininstr_instr,neutralActive])
    have remaining := ih (occurrence+1) label.after (fun l hm => hl l (by simp [hm]))
      (hl label (by simp)).2 nested.2 (fun l hm => heights l (by simp [hm]))
    simpa only [List.length_cons, List.nil_append] using ChosenStepsN.cons chosen remaining

/-- The actual return transition simulates to either the resumed caller or the
completed invocation, with no assumption about the desired reduction. -/
theorem chosen_typed_return_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ = .next next) :
    ChosenStepsN choices occurrence (f.labels.length + 1) (decode ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    have results := return_suffix_typed hf
    have count := resultsTyped_length results
    simp only [List.length_drop] at count
    have bound : f.arity ≤ f.vals.length := by unfold AFrame.arity; omega
    have heights : FrameHeights f := typed.heights { f with code := .RETURN :: after } (by simp)
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      have result := chosen_return_simulation admissible vector occurrence s ambient f rest f.labels after typed.store typed.ambient hw
        (codeStack_labels_wf hc) (resultsTyped_wf values)
        (fun i hm => codeStack_wf hc i (by simp [hm])) (framesTyped_wf hr)
        (codeStack_labels_nested hc) bound heights
      simp only [astep, returnFrame] at step
      split at step
      · cases rest with
        | nil =>
          simp only [AResult.next.injEq] at step
          rw [← step]
          exact result
        | cons caller callers =>
          simp only [advance, AResult.next.injEq] at step
          rw [← step, decode_resume s ambient caller callers _ (typed.heights caller (by simp))]
          exact result
      · contradiction

end Exec.Abs
