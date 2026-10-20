import Exec.Abs.Sim.Branch
import Exec.Abs.Sim.NeutralDecode
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_branch_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (labels : List Label) (after : List instr)
    (depth : Nat) (target : Label)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (nested : LabelsNested labels) (lookup : labels[depth]? = some target)
    (bound : ∀ label ∈ labels, label.height + target.arity ≤ f.vals.length)
    (hdepth : depth < 2 ^ 32) :
    ChosenStepsN choices occurrence (depth + 1) (decode ⟨s, ambient,
      { f with code := .BR (.mk_uN depth) :: after, labels := labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := target.cont ++ target.after, labels := labels.drop (depth + 1), vals := f.vals.take target.height ++ f.vals.drop (f.vals.length - target.arity) } :: rest, []⟩) := by
  induction depth generalizing labels after occurrence with
  | zero =>
    cases labels with
    | nil => simp at lookup
    | cons label labels =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst target
      have hb := bound label (by simp)
      let saved := f.vals.take label.height
      let discarded := (f.vals.drop label.height).take (f.vals.length - label.arity - label.height)
      let args := f.vals.drop (f.vals.length - label.arity)
      have hsplit := branch_values_split f.vals label.height label.arity hb
      have hstep := br_zero_simulation s ambient f rest label labels after saved discarded args hs ha hf hl
        (fun v hm => hv v (List.mem_of_mem_take hm))
        (fun v hm => hv v (List.mem_of_mem_drop (List.mem_of_mem_take hm)))
        (fun v hm => hv v (List.mem_of_mem_drop hm)) hc hr
        (by simp only [saved, List.length_take]; omega)
        (by simp only [args, List.length_drop]; omega)
        (by intro l hm; have hh := nested.1 l hm; simp only [saved, List.length_take]; omega)
      have hstep' : StepH (decode ⟨s, ambient, { f with code := .BR (.mk_uN 0) :: after, labels := label :: labels } :: rest, []⟩) []
          (decode ⟨s, ambient, { f with code := label.cont ++ label.after, labels := labels, vals := saved ++ args } :: rest, []⟩) := by
        simpa only [saved, discarded, args, ← hsplit] using hstep
      have chosen := chosen_neutral_simulation admissible vector occurrence hstep'
        (by simp only [List.map_cons,admininstr_instr,neutralActive])
      simpa only [List.nil_append, List.drop_succ_cons, List.drop_zero, saved, args] using
        ChosenStepsN.cons chosen (ChosenStepsN.refl (occurrence+1) (chosen.wf admissible).2)
  | succ depth ih =>
    cases labels with
    | nil => simp at lookup
    | cons label labels =>
      simp only [List.getElem?_cons_succ] at lookup
      have hb := bound label (by simp)
      let saved := f.vals.take label.height
      let operands := f.vals.drop label.height
      have first := br_succ_simulation s ambient f rest label labels after saved operands depth hs ha hf hl
        (fun v hm => hv v (List.mem_of_mem_take hm))
        (fun v hm => hv v (List.mem_of_mem_drop hm)) hc hr
        (by simp only [saved, List.length_take]; omega) hdepth
        (by intro l hm; have hh := nested.1 l hm; simp only [saved, List.length_take]; omega)
      have first' : StepH (decode ⟨s, ambient, { f with code := .BR (.mk_uN (depth + 1)) :: after, labels := label :: labels } :: rest, []⟩) []
          (decode ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: label.after, labels := labels } :: rest, []⟩) := by
        simpa only [saved, operands, List.take_append_drop] using first
      have chosen := chosen_neutral_simulation admissible vector occurrence first'
        (by simp only [List.map_cons,admininstr_instr,neutralActive])
      have remaining := ih (occurrence+1) labels label.after (fun l hm => hl l (by simp [hm]))
        (hl label (by simp)).2 nested.2 lookup (fun l hm => bound l (by simp [hm])) (by omega)
      simpa only [List.nil_append, List.drop_succ_cons, Nat.succ_eq_add_one] using ChosenStepsN.cons chosen remaining

/-- The branch simulation's address, height, arity, and well-formedness premises
follow from the actual source typing invariant. -/
theorem chosen_typed_branch_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (depth : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩ = .next next) :
    ChosenStepsN choices occurrence (depth + 1) (decode ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, heights⟩ := codeStack_head_bounds (value_types_concrete f.vals) hc
      cases hop with
      | br _ _ discarded types outputs hi ht hC hinst =>
        have hi' : depth < f.labels.length := by simpa [labelContext, proj_uN_0] using hi
        let target := f.labels[depth]
        have lookup : f.labels[depth]? = some target := List.getElem?_eq_getElem hi'
        have htypes : target.branchTypes = types := by
          simpa [target, labelContext, proj_uN_0, proj_list_0, getElem!_pos, hi'] using ht
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have bound : ∀ label ∈ f.labels, label.height + target.arity ≤ f.vals.length := by
          intro label hm
          have hh := heights label hm
          simp only [Label.arity, htypes]
          omega
        have hdepth : depth < 2 ^ 32 := by
          cases hinst with
          | instr_case_7 _ hu =>
            cases hu with
            | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
        have result := chosen_branch_simulation admissible vector occurrence s ambient f rest f.labels after depth target
          typed.store typed.ambient hw (codeStack_labels_wf hc) (resultsTyped_wf values)
          (fun i hm => codeStack_wf hc i (by simp [hm])) (framesTyped_wf hr)
          (codeStack_labels_nested hc) lookup bound hdepth
        simp only [astep, branch, lookup] at step
        split at step
        · simp only [advance, AResult.next.injEq] at step
          exact step ▸ result
        · contradiction

end Exec.Abs
