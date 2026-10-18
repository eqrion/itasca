import Exec.Abs.Sim.Control
import Exec.Abs.Sim.Typing
import Exec.Spec.Counted

namespace Exec.Abs
open SpecExt Exec.Spec

/-- Branching to the innermost label discards its intermediate operands and
resumes the declared continuation with exactly the branch results. -/
theorem br_zero_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label) (after : List instr)
    (saved discarded args : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf (label :: labels)) (hv : Forall wf_val saved)
    (hd : Forall wf_val discarded) (hargs : Forall wf_val args)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (height : label.height = saved.length) (arity : label.arity = args.length)
    (heights : ∀ outer ∈ labels, outer.height ≤ saved.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .BR (.mk_uN 0) :: after, vals := saved ++ (discarded ++ args), labels := label :: labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := label.cont ++ label.after, vals := saved ++ args, labels := labels } :: rest, []⟩) := by
  have hlabel := hl label (by simp)
  have htail : LabelsWf labels := fun l hm => hl l (by simp [hm])
  have hbr : wf_admininstr (.BR (.mk_uN 0)) := .admininstr_case_7 _ (integer_uN_wf .I32 0 (by decide))
  let redex := ((vals discarded ++ vals args) ++ [.BR (.mk_uN 0)]) ++ after.map admininstr_instr
  have hredex : Forall wf_admininstr redex :=
    forall_append (forall_append (forall_append (wf_vals hd) (wf_vals hargs))
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hbr)) (wf_instrs hc)
  have hwrap : wf_admininstr (.LABEL_ label.arity label.cont redex) := .admininstr_case_71 _ _ _ hlabel.1 hredex
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont redex]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, vals args ++ label.cont.map admininstr_instr⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs) (wf_instrs hlabel.1))
  have step : StepH ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont redex]⟩ []
      ⟨⟨s, f.toFrame⟩, vals args ++ label.cont.map admininstr_instr⟩ :=
    .step (.pure _ _ _ (.br_zero _ _ _ _ _ hwrap arity) hsource htarget)
  have h₁ := stepH_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := stepH_decodeLabels h₁ labels saved htail hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    List.map_append, AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeLabels, height, Label.arity, redex, instrContext, vals, List.map_append,
    List.append_assoc, AFrame.toFrame, AFrame.arity, admininstr_instr] using h₃

/-- Crossing one enclosing label decrements the branch depth by one. This
retains all current operands until the target label selects its result suffix. -/
theorem br_succ_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label) (after : List instr)
    (saved operands : List val) (depth : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf (label :: labels)) (hv : Forall wf_val saved) (hargs : Forall wf_val operands)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (height : label.height = saved.length) (hdepth : depth + 1 < 2 ^ 32)
    (heights : ∀ outer ∈ labels, outer.height ≤ saved.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .BR (.mk_uN (depth + 1)) :: after, vals := saved ++ operands, labels := label :: labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := .BR (.mk_uN depth) :: label.after, vals := saved ++ operands, labels := labels } :: rest, []⟩) := by
  have hlabel := hl label (by simp)
  have htail : LabelsWf labels := fun l hm => hl l (by simp [hm])
  have hbr : wf_admininstr (.BR (.mk_uN (depth + 1))) := .admininstr_case_7 _ (integer_uN_wf .I32 _ hdepth)
  have hbr' : wf_admininstr (.BR (.mk_uN depth)) := .admininstr_case_7 _ (integer_uN_wf .I32 _ (by simp only [integerWidth]; omega))
  let redex := (vals operands ++ [.BR (.mk_uN (depth + 1))]) ++ after.map admininstr_instr
  have hredex : Forall wf_admininstr redex :=
    forall_append (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hbr)) (wf_instrs hc)
  have hwrap : wf_admininstr (.LABEL_ label.arity label.cont redex) := .admininstr_case_71 _ _ _ hlabel.1 hredex
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont redex]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [.BR (.mk_uN depth)]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hbr'))
  have step : StepH ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont redex]⟩ []
      ⟨⟨s, f.toFrame⟩, vals operands ++ [.BR (.mk_uN depth)]⟩ :=
    .step (.pure _ _ _ (.br_succ _ _ _ (.mk_uN depth) _ hwrap hbr') hsource htarget)
  have h₁ := stepH_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := stepH_decodeLabels h₁ labels saved htail hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    List.map_append, AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeLabels, height, Label.arity, redex, instrContext, vals, List.map_append,
    List.append_assoc, AFrame.toFrame, AFrame.arity, admininstr_instr] using h₃

/-- Absolute label heights are nonincreasing toward enclosing contexts. -/
def LabelsNested : List Label → Prop
  | [] => True
  | label :: labels => (∀ outer ∈ labels, outer.height ≤ label.height) ∧ LabelsNested labels

theorem codeStack_labels_nested {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) : LabelsNested labels := by
  induction h with
  | outer => trivial
  | label _ nesting _ _ _ ih => exact ⟨nesting, ih⟩

theorem branch_values_split (values : List val) (height arity : Nat)
    (bound : height + arity ≤ values.length) :
    values = values.take height ++
      ((values.drop height).take (values.length - arity - height) ++ values.drop (values.length - arity)) := by
  have h := List.take_append_drop (values.length - arity - height) (values.drop height)
  rw [List.drop_drop, show height + (values.length - arity - height) = values.length - arity by omega] at h
  rw [h]
  exact (List.take_append_drop height values).symm

/-- A branch crossing `depth` inner labels takes exactly `depth + 1` source
steps, and resumes the target's continuation with its declared result suffix. -/
theorem branch_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (labels : List Label) (after : List instr)
    (depth : Nat) (target : Label)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (nested : LabelsNested labels) (lookup : labels[depth]? = some target)
    (bound : ∀ label ∈ labels, label.height + target.arity ≤ f.vals.length)
    (hdepth : depth < 2 ^ 32) :
    StepsHN (depth + 1) (decode ⟨s, ambient,
      { f with code := .BR (.mk_uN depth) :: after, labels := labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := target.cont ++ target.after, labels := labels.drop (depth + 1), vals := f.vals.take target.height ++ f.vals.drop (f.vals.length - target.arity) } :: rest, []⟩) := by
  induction depth generalizing labels after with
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
      simpa only [List.nil_append, List.drop_succ_cons, List.drop_zero, saved, args] using
        StepsHN.cons hstep' (StepsHN.refl (stepH_wf hstep').2)
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
      have remaining := ih labels label.after (fun l hm => hl l (by simp [hm]))
        (hl label (by simp)).2 nested.2 lookup (fun l hm => bound l (by simp [hm])) (by omega)
      simpa only [List.nil_append, List.drop_succ_cons, Nat.succ_eq_add_one] using StepsHN.cons first' remaining

/-- The branch simulation's address, height, arity, and well-formedness premises
follow from the actual source typing invariant. -/
theorem typed_branch_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (depth : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩ = .next next) :
    StepsHN (depth + 1) (decode ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩) [] (decode next) := by
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
        have result := branch_simulation s ambient f rest f.labels after depth target
          typed.store typed.ambient hw (codeStack_labels_wf hc) (resultsTyped_wf values)
          (fun i hm => codeStack_wf hc i (by simp [hm])) (framesTyped_wf hr)
          (codeStack_labels_nested hc) lookup bound hdepth
        simp only [astep, branch, lookup] at step
        split at step
        · simp only [advance, AResult.next.injEq] at step
          exact step ▸ result
        · contradiction

end Exec.Abs
