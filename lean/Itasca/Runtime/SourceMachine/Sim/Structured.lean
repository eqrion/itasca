import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.Typing
import Itasca.Runtime.SourceMachine.Bound

/-!
Sections, each formerly its own module: Branch, Return, Call, Local, Typed, Structured.
-/

/-! ## Branch -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

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
  have hbr : wf_admininstr (.BR (.mk_uN 0)) := .admininstr_case_7 _ (integer_u_n_wf .I32 0 (by decide))
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
  have h₁ := step_h_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := step_h_decode_labels h₁ labels saved htail hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    List.map_append, AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
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
  have hbr : wf_admininstr (.BR (.mk_uN (depth + 1))) := .admininstr_case_7 _ (integer_u_n_wf .I32 _ hdepth)
  have hbr' : wf_admininstr (.BR (.mk_uN depth)) := .admininstr_case_7 _ (integer_u_n_wf .I32 _ (by simp only [integerWidth]; omega))
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
  have h₁ := step_h_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := step_h_decode_labels h₁ labels saved htail hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    List.map_append, AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeLabels, height, Label.arity, redex, instrContext, vals, List.map_append,
    List.append_assoc, AFrame.toFrame, AFrame.arity, admininstr_instr] using h₃

/-- Absolute label heights are nonincreasing toward enclosing contexts. -/
def LabelsNested : List Label → Prop
  | [] => True
  | label :: labels => (∀ outer ∈ labels, outer.height ≤ label.height) ∧ LabelsNested labels

theorem code_stack_labels_nested {C : context} {labels : List Label}
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
        StepsHN.cons hstep' (StepsHN.refl (step_h_wf hstep').2)
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
      obtain ⟨front, ins, outs, hop, hstack, heights⟩ := code_stack_head_bounds (value_types_concrete f.vals) hc
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
          typed.store typed.ambient hw (code_stack_labels_wf hc) (results_typed_wf values)
          (fun i hm => code_stack_wf hc i (by simp [hm])) (frames_typed_wf hr)
          (code_stack_labels_nested hc) lookup bound hdepth
        simp only [astep, branch, lookup] at step
        split at step
        · simp only [advance, AResult.next.injEq] at step
          exact step ▸ result
        · contradiction

end Itasca.Runtime.SourceMachine

end

/-! ## Return -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Appending a callee's results to its suspended caller agrees with inserting
those values into the decoded frame context. Saved prefixes already exist. -/
theorem decode_resume (s : store) (ambient : frame) (caller : AFrame)
    (rest : List AFrame) (values : List val) (heights : FrameHeights caller) :
    decode ⟨s, ambient, { caller with vals := caller.vals ++ values } :: rest, []⟩ =
      ⟨⟨s, ambient⟩, decodeFrames (caller :: rest) (vals values)⟩ := by
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  rfl

theorem frame_end_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (hs : wf_store s) (ha : wf_frame ambient)
    (hf : wf_frame f.toFrame) (hv : Forall wf_val f.vals) (hr : Forall FrameWf rest)
    (arity : f.arity = f.vals.length) :
    StepH (decode ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, decodeFrames rest (vals f.vals)⟩ := by
  have hwrap : wf_admininstr (.FRAME_ f.arity f.toFrame (vals f.vals)) :=
    .admininstr_case_72 _ _ _ hf (wf_vals hv)
  have hsource : wf_config ⟨⟨s, activeFrame ambient rest⟩, [.FRAME_ f.arity f.toFrame (vals f.vals)]⟩ :=
    wf_config_make hs (active_frame_wf ha hr)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget := wf_config_vals hs (active_frame_wf ha hr) hv
  have step : StepH ⟨⟨s, activeFrame ambient rest⟩, [.FRAME_ f.arity f.toFrame (vals f.vals)]⟩ []
      ⟨⟨s, activeFrame ambient rest⟩, vals f.vals⟩ :=
    .step (.pure _ _ _ (.frame_vals _ _ _ hwrap arity) hsource htarget)
  simpa [decode, decodeFrames, decodeLabels, vals, AFrame.toFrame, AFrame.arity] using
    step_h_decode_frames ambient rest step ha hr

/-- Explicit return at the outer function scope discards earlier operands and
resumes the caller with exactly the function's result arity. -/
theorem return_frame_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (discarded results : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hd : Forall wf_val discarded) (hv : Forall wf_val results)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (arity : f.arity = results.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .RETURN :: after, labels := [], vals := discarded ++ results } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, decodeFrames rest (vals results)⟩ := by
  let redex := ((vals discarded ++ vals results) ++ [.RETURN]) ++ after.map admininstr_instr
  have hredex : Forall wf_admininstr redex :=
    forall_append (forall_append (forall_append (wf_vals hd) (wf_vals hv))
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_12)) (wf_instrs hc)
  have hwrap : wf_admininstr (.FRAME_ f.arity f.toFrame redex) := .admininstr_case_72 _ _ _ hf hredex
  have hsource : wf_config ⟨⟨s, activeFrame ambient rest⟩, [.FRAME_ f.arity f.toFrame redex]⟩ :=
    wf_config_make hs (active_frame_wf ha hr)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget := wf_config_vals hs (active_frame_wf ha hr) hv
  have step : StepH ⟨⟨s, activeFrame ambient rest⟩, [.FRAME_ f.arity f.toFrame redex]⟩ []
      ⟨⟨s, activeFrame ambient rest⟩, vals results⟩ :=
    .step (.pure _ _ _ (.return_frame _ _ _ _ _ hwrap arity) hsource htarget)
  simpa [decode, decodeFrames, decodeLabels, redex, vals, List.map_append,
    List.append_assoc, admininstr_instr, AFrame.toFrame, AFrame.arity] using
    step_h_decode_frames ambient rest step ha hr

theorem return_label_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label) (after : List instr)
    (saved operands : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf (label :: labels)) (hv : Forall wf_val saved) (hargs : Forall wf_val operands)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (height : label.height = saved.length)
    (heights : ∀ outer ∈ labels, outer.height ≤ saved.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .RETURN :: after, vals := saved ++ operands, labels := label :: labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := .RETURN :: label.after, vals := saved ++ operands, labels := labels } :: rest, []⟩) := by
  have hlabel := hl label (by simp)
  have htail : LabelsWf labels := fun l hm => hl l (by simp [hm])
  have hbr : wf_admininstr (.RETURN) := .admininstr_case_12
  let redex := (vals operands ++ [.RETURN]) ++ after.map admininstr_instr
  have hredex : Forall wf_admininstr redex :=
    forall_append (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hbr)) (wf_instrs hc)
  have hwrap : wf_admininstr (.LABEL_ label.arity label.cont redex) := .admininstr_case_71 _ _ _ hlabel.1 hredex
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont redex]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [.RETURN]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hbr))
  have step : StepH ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont redex]⟩ []
      ⟨⟨s, f.toFrame⟩, vals operands ++ [.RETURN]⟩ :=
    .step (.pure _ _ _ (.return_label _ _ _ _ hwrap hbr) hsource htarget)
  have h₁ := step_h_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := step_h_decode_labels h₁ labels saved htail hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    List.map_append, AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeLabels, height, Label.arity, redex, instrContext, vals, List.map_append,
    List.append_assoc, AFrame.toFrame, AFrame.arity, admininstr_instr] using h₃


/-- Explicit return crosses each label once and then removes its function
frame, retaining an exact positive reduction count. -/
theorem return_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (labels : List Label) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (nested : LabelsNested labels) (bound : f.arity ≤ f.vals.length)
    (heights : ∀ label ∈ labels, label.height ≤ f.vals.length) :
    StepsHN (labels.length + 1) (decode ⟨s, ambient,
      { f with code := .RETURN :: after, labels := labels } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, decodeFrames rest (vals (f.vals.drop (f.vals.length - f.arity)))⟩ := by
  induction labels generalizing after with
  | nil =>
    have step := return_frame_simulation s ambient f rest after
      (f.vals.take (f.vals.length - f.arity)) (f.vals.drop (f.vals.length - f.arity))
      hs ha hf (fun v hm => hv v (List.mem_of_mem_take hm))
      (fun v hm => hv v (List.mem_of_mem_drop hm)) hc hr
      (by simp only [List.length_drop]; omega)
    simpa only [List.take_append_drop, List.length_nil, List.nil_append] using
      StepsHN.cons step (StepsHN.refl (step_h_wf step).2)
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
    have remaining := ih label.after (fun l hm => hl l (by simp [hm]))
      (hl label (by simp)).2 nested.2 (fun l hm => heights l (by simp [hm]))
    simpa only [List.length_cons, List.nil_append] using StepsHN.cons first' remaining

/-- The actual return transition simulates to either the resumed caller or the
completed invocation, with no assumption about the desired reduction. -/
theorem typed_return_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ = .next next) :
    StepsHN (f.labels.length + 1) (decode ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    have results := return_suffix_typed hf
    have count := results_typed_length results
    simp only [List.length_drop] at count
    have bound : f.arity ≤ f.vals.length := by unfold AFrame.arity; omega
    have heights : FrameHeights f := typed.heights { f with code := .RETURN :: after } (by simp)
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      have result := return_simulation s ambient f rest f.labels after typed.store typed.ambient hw
        (code_stack_labels_wf hc) (results_typed_wf values)
        (fun i hm => code_stack_wf hc i (by simp [hm])) (frames_typed_wf hr)
        (code_stack_labels_nested hc) bound heights
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

theorem typed_frame_end_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ = .next next) :
    StepH (decode ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    have values := frame_end_typed hf
    have count := results_typed_length values
    have arity : f.arity = f.vals.length := count.symm
    have result := frame_end_simulation s ambient f rest typed.store typed.ambient
      (frame_typed_wf hf).1 (results_typed_wf values) (frames_typed_wf hr) arity
    simp only [astep, returnFrame] at step
    split at step
    · cases rest with
      | nil =>
        simp only [arity, Nat.sub_self, List.drop_zero, AResult.next.injEq] at step
        rw [← step]
        simpa only [AFrame.arity, ← count, Nat.sub_self, List.drop_zero, decode, decodeFrames] using result
      | cons caller callers =>
        simp only [arity, Nat.sub_self, List.drop_zero, advance, AResult.next.injEq] at step
        rw [← step, decode_resume s ambient caller callers _ (typed.heights caller (by simp))]
        simpa only [AFrame.arity, ← count, Nat.sub_self, List.drop_zero] using result
    · contradiction

end Itasca.Runtime.SourceMachine

end

/-! ## Call -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem default_value_relation (ty : valtype) (h : ty ≠ .BOT) :
    fun_default_ ty (defaultValue ty) := by
  cases ty with
  | I32 => exact .fun_default__case_0 (integer_val_wf .I32 0 (by decide))
  | I64 => exact .fun_default__case_1 (integer_val_wf .I64 0 (by decide))
  | F32 =>
    exact .fun_default__case_2 _ (.fun_fzero_case_0 _
      (.fN_case_0 _ _ (.fNmag_case_1 _ _ _ ⟨by positivity, rfl⟩))) (zero_float_wf .F32)
  | F64 =>
    exact .fun_default__case_3 _ (.fun_fzero_case_0 _
      (.fN_case_0 _ _ (.fNmag_case_1 _ _ _ ⟨by positivity, rfl⟩))) (zero_float_wf .F64)
  | V128 => exact .fun_default__case_4 (.val_case_1 _ _ (by decide) (.uN_case_0 _ _ ⟨by omega, by omega⟩))
  | FUNCREF => exact .fun_default__case_5 (.val_case_2 _)
  | EXTERNREF => exact .fun_default__case_6 (.val_case_2 _)
  | BOT => contradiction

theorem default_locals_relation {s : store} (hs : wf_store s) (types : List valtype)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types) (values : List val)
    (h : defaultLocals (types.map local.LOCAL) = some values) :
    List.Forall₂ (fun value ty => fun_default_ ty (some value)) values types := by
  induction types generalizing values with
  | nil => simp only [List.map_nil, defaultLocals, Option.some.injEq] at h; subst values; exact .nil
  | cons ty types ih =>
    obtain ⟨value, hv, _⟩ := default_value_typed hs ty (nonbot ty (by simp))
    have relation := default_value_relation ty (nonbot ty (by simp))
    rw [hv] at relation
    cases rest : defaultLocals (types.map local.LOCAL) with
    | none => simp [defaultLocals, hv, rest] at h
    | some tail =>
      simp [defaultLocals, hv, rest] at h
      subst values
      exact .cons relation (ih (fun ty ht => nonbot ty (by simp [ht])) tail rest)

theorem defaults_forall₂ {values : List val} {types : List valtype}
    (h : List.Forall₂ (fun value ty => fun_default_ ty (some value)) values types) :
    Forall₂ (fun value ty => fun_default_ ty value) (values.map some) types := by
  induction h with
  | nil => simp [Forall₂]
  | @cons value ty values types relation rest ih =>
    intro pair hp
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact relation
    · exact ih pair hp

/-- The first call reduction resolves the active module's actual function map. -/
theorem call_resolve (s : store) (f : frame) (index address : Nat)
    (hs : wf_store s) (hf : wf_frame f)
    (lookup : f.MODULE.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32) :
    StepH ⟨⟨s, f⟩, [.CALL (.mk_uN index)]⟩ [] ⟨⟨s, f⟩, [.CALL_ADDR address]⟩ := by
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp lookup
  have hsource : wf_config ⟨⟨s, f⟩, [.CALL (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by
      intro i hm; simp only [List.mem_singleton] at hm; subst i
      exact .admininstr_case_10 _ (integer_u_n_wf .I32 index hi32))
  have htarget : wf_config ⟨⟨s, f⟩, [.CALL_ADDR address]⟩ :=
    wf_config_make hs hf (by intro i hm; simp only [List.mem_singleton] at hm; subst i; exact .admininstr_case_70 _)
  apply StepH.step
  apply Step.read _ _ _ ?_ hsource htarget
  simpa only [fun_funcaddr, proj_uN_0, getElem!_pos f.MODULE.FUNCS index hi, heq] using
    Step_read.call ⟨s, f⟩ (.mk_uN index) hi hsource (.admininstr_case_70 _)

theorem store_function_wf {s : store} (hs : wf_store s) {fn : funcinst}
    (hm : fn ∈ s.FUNCS) : wf_funcinst fn := by
  cases hs with | store_case_ _ _ _ _ _ _ funcs _ _ _ _ => exact funcs fn hm

/-- The address call rule creates exactly the callee frame and result label,
using the concrete declared local defaults. -/
theorem call_invoke (s : store) (f : frame) (address : Nat) (index : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (args defaults : List val) (hs : wf_store s) (hf : wf_frame f)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC index (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR address]⟩ []
      ⟨⟨s, f⟩, [.FRAME_ results.length ⟨args ++ defaults, moduleInst⟩
        [.LABEL_ results.length [] (body.map admininstr_instr)]]⟩ := by
  obtain ⟨hi, hlookup⟩ := List.getElem?_eq_some_iff.mp lookup
  have hfn := store_function_wf hs (List.mem_of_getElem? lookup)
  have hm := function_module_wf hs (List.mem_of_getElem? lookup)
  have hfunc : wf_func (.FUNC index (types.map local.LOCAL) body) := by
    cases hfn with
    | funcinst_case_ _ _ _ _ hc =>
      cases hc with | funccode_case_0 _ _ _ hi hb => exact .func_case_0 _ _ _ hi hb
  have hbody : Forall wf_instr body := by cases hfunc; assumption
  obtain ⟨values, hv, hvalues⟩ := default_locals_typed hs types nonbot
  have heq : values = defaults := Option.some.inj (hv.symm.trans hdefaults)
  subst values
  have hdlen := results_typed_length hvalues
  have hlocals := forall_append hargs (results_typed_wf hvalues)
  have hframe : wf_frame ⟨args ++ defaults, moduleInst⟩ := .frame_case_ _ _ hlocals hm
  have hlabel : wf_admininstr (.LABEL_ results.length [] (body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (forall_nil _) (wf_instrs hbody)
  have hwrap : wf_admininstr (.FRAME_ results.length ⟨args ++ defaults, moduleInst⟩
      [.LABEL_ results.length [] (body.map admininstr_instr)]) :=
    .admininstr_case_72 _ _ _ hframe (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hlabel)
  have hsource : wf_config ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR address]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_70 _))
  have htarget : wf_config ⟨⟨s, f⟩, [.FRAME_ results.length ⟨args ++ defaults, moduleInst⟩
      [.LABEL_ results.length [] (body.map admininstr_instr)]]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  apply StepH.step
  apply Step.read _ _ _ ?_ hsource htarget
  apply Step_read.call_addr ⟨s, f⟩ args.length args address results.length
    ⟨args ++ defaults, moduleInst⟩ body params results moduleInst
    (.FUNC index (types.map local.LOCAL) body) index types (defaults.map some)
  · simpa only [List.length_map] using hdlen
  · exact defaults_forall₂ (default_locals_relation hs types nonbot defaults hdefaults)
  · exact hi
  · simpa only [fun_funcinst, funccode_func, getElem!_pos s.FUNCS address hi] using hlookup
  · rfl
  · intro value hv
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
    simp
  · simp [Map, List.map_map, Function.comp_def, Option.get!]
  · exact hsource
  · exact hwrap
  · exact hfn
  · exact hfunc
  · simpa [Map, List.map_map, Function.comp_def, Option.get!] using hframe
  · rfl
  · exact hlen
  · rfl

/-- A defined direct call resolves its address, then installs the actual callee
frame. The caller's operands and all suspended contexts are preserved. -/
theorem call_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat) (typeIndex : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (baseValues args defaults : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    StepsHN 2
      (decode ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have h₁ := step_h_instrs (call_resolve s f.toFrame index address hs hf resolve hi32)
    args (after.map admininstr_instr) hargs (wf_instrs hc)
  have h₂ := step_h_instrs (call_invoke s f.toFrame address typeIndex moduleInst
    params results types body args defaults hs hf lookup nonbot hdefaults hargs hlen)
    [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₃ := step_h_active ambient rest f.arity
    (step_h_decode_labels h₁ f.labels baseValues hl hv) ha hr
  have h₄ := step_h_active ambient rest f.arity
    (step_h_decode_labels h₂ f.labels baseValues hl hv) ha hr
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc] at h₃ h₄
  have both := StepsHN.cons h₃ (StepsHN.cons h₄ (StepsHN.refl (step_h_wf h₄).2))
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, decodeLabels, Label.arity, List.take_zero,
    List.drop_zero, List.append_nil]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr] using both

theorem function_local_types {C : context} {index : idx} {locals : List «local»}
    {body : List instr} {ft : functype} (h : Func_ok C (.FUNC index locals body) ft) :
    ∃ types, locals = types.map local.LOCAL ∧ Forall (fun ty => ty ≠ valtype.BOT) types := by
  cases h
  exact ⟨_, rfl, by assumption⟩

/-- No operational call premise is postulated: address resolution, signature,
local defaults, and stack arguments follow from the source typing invariant. -/
theorem typed_call_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩ = .next next) :
    StepsHN 2 (decode ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        code_stack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht hC hinst =>
        simp only [labelContext, proj_uN_0] at hi ht
        have hi' : index < f.module.FUNCS.length := by
          rw [bindings.funcs.length_eq]
          exact hi
        obtain ⟨fn, hfn, htype⟩ := bindings.funcs.get hi' hi
        simp only [List.get_eq_getElem] at hfn htype
        have htype' : fn.TYPE = ⟨.mk_list ins, .mk_list outs⟩ := by
          rw [htype]
          simpa only [getElem!_pos C.FUNCS index hi] using ht
        have hresolve := List.getElem?_eq_getElem hi'
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - ins.length = front.length := by omega
        have hbound : ins.length ≤ f.vals.length := by omega
        have hargs : ResultsTyped s ins (f.vals.drop front.length) := by
          apply results_typed_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hi32 : index < 2 ^ 32 := by
          cases hinst with
          | instr_case_10 _ hu => cases hu with
            | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
        cases hcode : fn.CODE with
        | HOST host =>
          simp [astep, call, hresolve, hfn, htype', hbound, hheight, hargtypes, hcode] at step
        | FUNC fi fl body =>
          have htyped := typed.functions fn (List.mem_of_getElem? hfn)
          simp only [hcode] at htyped
          obtain ⟨Cfn, hbindings, hlocals, hlabels, _, hfunc⟩ := htyped
          rw [htype'] at hfunc
          obtain ⟨types, hfl, nonbot⟩ := function_local_types hfunc
          subst fl
          obtain ⟨defaults, hdefaults, hdefaultTypes⟩ := default_locals_typed typed.store types nonbot
          have hrecord : fn = ⟨⟨.mk_list ins, .mk_list outs⟩, fn.MODULE,
              .FUNC fi (types.map local.LOCAL) body⟩ := by
            cases fn
            simp_all
          have result := call_simulation s ambient f rest after index (f.module.FUNCS[index]) fi
            fn.MODULE ins outs types body (f.vals.take front.length) (f.vals.drop front.length) defaults
            typed.store typed.ambient hw (code_stack_labels_wf hc)
            (fun v hv => results_typed_wf values v (List.mem_of_mem_take hv))
            (fun i hm => code_stack_wf hc i (by simp [hm])) (frames_typed_wf hr)
            (by intro label hm; have hh := heights label hm; simp only [List.length_take]; omega)
            hresolve hi32 (hrecord ▸ hfn) nonbot hdefaults (results_typed_wf hargs) (results_typed_length hargs)
          have hnext : next = ⟨s, ambient,
              ⟨f.module.FUNCS[index], outs, f.vals.drop front.length ++ defaults, fn.MODULE,
                [⟨outs, outs, [], 0, []⟩], body, []⟩ ::
              { f with vals := f.vals.take front.length, code := after } :: rest, []⟩ := by
            simpa [astep, call, hresolve, hfn, htype', hbound, hheight, hargtypes, hcode, hdefaults] using step.symm
          rw [hnext]
          simpa only [List.take_append_drop] using result

end Itasca.Runtime.SourceMachine

end

/-! ## Local -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The read uses the active frame's locals, then lifts through every surrounding
label and caller. Bounds and syntax well-formedness remain explicit. -/
theorem local_get_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (hi : index < f.locals.length) (hi32 : index < 2 ^ 32) :
    StepH (decode ⟨s, ambient,
      { f with code := .LOCAL_GET (.mk_uN index) :: after } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [f.locals[index]!] } :: rest, []⟩) := by
  have hlocals : Forall wf_val f.locals := by
    cases hf with | frame_case_ _ _ hlocals _ => exact hlocals
  have hvalue : wf_val f.locals[index]! := by
    simpa only [getElem!_pos f.locals index hi] using hlocals _ (List.getElem_mem hi)
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [.LOCAL_GET (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by
      intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      exact .admininstr_case_43 _ (integer_u_n_wf .I32 index hi32))
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, [admininstr_val f.locals[index]!]⟩ :=
    wf_config_make hs hf (by
      intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      exact wf_admininstr_val hvalue)
  have step : StepH ⟨⟨s, f.toFrame⟩, [.LOCAL_GET (.mk_uN index)]⟩ []
      ⟨⟨s, f.toFrame⟩, [admininstr_val f.locals[index]!]⟩ := by
    apply StepH.step
    apply Step.read _ _ _ ?_ hsource htarget
    simpa only [fun_local, AFrame.toFrame, proj_uN_0] using
      (Step_read.local_get (.mk_state s f.toFrame) (.mk_uN index) hsource)
  simpa using stack_step_simulation s ambient f rest (.LOCAL_GET (.mk_uN index)) after
    f.vals [] [f.locals[index]!] ha hl hv hc hr heights step

theorem forall_set {α : Type} {P : α → Prop} {values : List α}
    (h : Forall P values) (index : Nat) (value : α) (hv : P value) :
    Forall P (values.set index value) := by
  induction values generalizing index with
  | nil => exact forall_nil _
  | cons x xs ih =>
    cases index with
    | zero =>
      intro y hy
      simp only [List.set_cons_zero, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hv
      · exact h y (by simp [hy])
    | succ index =>
      intro y hy
      simp only [List.set_cons_succ, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h _ (by simp)
      · exact ih (fun z hz => h z (by simp [hz])) index y hy

/-- A local write changes the active frame's locals and is lifted through all
saved labels and callers without changing their local environments. -/
theorem local_set_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (value : val) (index : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hx : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hi32 : index < 2 ^ 32) :
    StepH (decode ⟨s, ambient,
      { f with code := .LOCAL_SET (.mk_uN index) :: after, vals := baseValues ++ [value] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, locals := f.locals.set index value, vals := baseValues } :: rest, []⟩) := by
  have hf' : wf_frame { f.toFrame with LOCALS := f.locals.set index value } := by
    cases hf with
    | frame_case_ _ _ locals moduleWf => exact .frame_case_ _ _ (forall_set locals index value hx) moduleWf
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [admininstr_val value, .LOCAL_SET (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact wf_admininstr_val hx
      · exact .admininstr_case_44 _ (integer_u_n_wf .I32 index hi32))
  have htarget : wf_config ⟨⟨s, { f.toFrame with LOCALS := f.locals.set index value }⟩, []⟩ :=
    wf_config_make hs hf' (forall_nil _)
  have relation : fun_with_local ⟨s, f.toFrame⟩ (.mk_uN index) value
      ⟨s, { f.toFrame with LOCALS := f.locals.set index value }⟩ := by
    simpa only [proj_uN_0, ← List.set_eq_modify, AFrame.toFrame] using
      (fun_with_local.fun_with_local_case_0 s f.toFrame (.mk_uN index) value (by
        simpa only [proj_uN_0, ← List.set_eq_modify, AFrame.toFrame] using wf_state.state_case_0 _ _ hs hf'))
  have step : StepH ⟨⟨s, f.toFrame⟩, [admininstr_val value, .LOCAL_SET (.mk_uN index)]⟩ []
      ⟨⟨s, { f.toFrame with LOCALS := f.locals.set index value }⟩, []⟩ :=
    .step (.local_set _ _ _ _ relation hsource htarget)
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr] using h₃

/-- local.tee performs the generated duplication rule followed by local.set;
the exact two-step count is retained for quantitative simulation. -/
theorem local_tee_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (value : val) (index : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hx : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hi32 : index < 2 ^ 32) :
    StepsHN 2 (decode ⟨s, ambient,
      { f with code := .LOCAL_TEE (.mk_uN index) :: after, vals := baseValues ++ [value] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, locals := f.locals.set index value, vals := baseValues ++ [value] } :: rest, []⟩) := by
  have hi := integer_u_n_wf .I32 index hi32
  have htee : wf_admininstr (.LOCAL_TEE (.mk_uN index)) := .admininstr_case_45 _ hi
  have hset : wf_admininstr (.LOCAL_SET (.mk_uN index)) := .admininstr_case_44 _ hi
  have hvalue := wf_admininstr_val hx
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [admininstr_val value, .LOCAL_TEE (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption)
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, [admininstr_val value, admininstr_val value, .LOCAL_SET (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> assumption)
  have step : StepH ⟨⟨s, f.toFrame⟩, [admininstr_val value, .LOCAL_TEE (.mk_uN index)]⟩ []
      ⟨⟨s, f.toFrame⟩, [admininstr_val value, admininstr_val value, .LOCAL_SET (.mk_uN index)]⟩ :=
    .step (.pure _ _ _ (.local_tee value (.mk_uN index) hx htee hset) hsource htarget)
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  have expanded : StepH (decode ⟨s, ambient,
      { f with code := .LOCAL_TEE (.mk_uN index) :: after, vals := baseValues ++ [value] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := .LOCAL_SET (.mk_uN index) :: after, vals := (baseValues ++ [value]) ++ [value] } :: rest, []⟩) := by
    simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
      AFrame.toFrame, AFrame.arity]
    rw [decode_labels_move_values _ _ _ _ heights]
    rw [List.append_assoc, decode_labels_move_values _ _ _ _ heights]
    simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr] using h₃
  have valuesWf : Forall wf_val (baseValues ++ [value]) := forall_append hv (by
    intro x hx'; simp only [List.mem_singleton] at hx'; subst x; exact hx)
  have heights' : ∀ label ∈ f.labels, label.height ≤ (baseValues ++ [value]).length := by
    intro label h; have hh := heights label h; simp only [List.length_append, List.length_singleton]; omega
  have write := local_set_simulation s ambient f rest after (baseValues ++ [value]) value index
    hs ha hf hl valuesWf hx hc hr heights' hi32
  exact .cons expanded (.cons write (.refl (step_h_wf write).2))

end Itasca.Runtime.SourceMachine

end

/-! ## Typed -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- A successful abstract step either performs positive source work or is an
exact decoding stutter that strictly decreases the administrative potential. -/
def NextSim (s next : AState) : Prop :=
  (decode s = decode next ∧ administrativeMeasure next < administrativeMeasure s) ∨
  ∃ n, 0 < n ∧ StepsHN n (decode s) [] (decode next)

theorem NextSim.single {s next : AState} (h : StepH (decode s) [] (decode next)) : NextSim s next :=
  Or.inr ⟨1, by omega, by simpa only [List.nil_append] using StepsHN.cons h (StepsHN.refl (step_h_wf h).2)⟩

theorem NextSim.counted {s next : AState} {n : Nat}
    (h : StepsHN n (decode s) [] (decode next)) (hn : 0 < n) : NextSim s next :=
  Or.inr ⟨n, hn, h⟩

/-- Operand inversion also proves that no consumed value belongs to a saved
outer label prefix. -/
theorem frame_typed_operands_bounds {s : store} {f : AFrame} {op : instr} {code : List instr}
    (h : FrameTyped s { f with code := op :: code } []) :
    ∃ C first operands ins outs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      f.vals = first ++ operands ∧ ResultsTyped s ins operands ∧
      Forall wf_val first ∧ (∀ label ∈ f.labels, label.height ≤ first.length) := by
  cases h with
  | mk C bindings locals hlocals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, heq, heights⟩ := code_stack_head_bounds (value_types_concrete f.vals) hc
    have values' : ResultsTyped s (front ++ ins) f.vals := by rw [← heq]; exact values
    obtain ⟨first, operands, hsplit, hfirst, hoperands⟩ := results_typed_split values'
    refine ⟨C, first, operands, ins, outs, bindings, locals, hop, hsplit, hoperands,
      results_typed_wf hfirst, ?_⟩
    intro label hm
    rw [results_typed_length hfirst]
    exact heights label hm

end Itasca.Runtime.SourceMachine

end

/-! ## Structured -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem block_type_spec (s : store) (f : AFrame) (bt : blocktype) (ft : functype)
    (h : blockType f.module bt = some ft) : fun_blocktype ⟨s, f.toFrame⟩ bt = ft := by
  cases bt with
  | _RESULT result => cases result <;> simpa only [blockType, fun_blocktype, Option.some.injEq] using h
  | _IDX index =>
    cases index with
    | mk_uN i =>
      obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp h
      simpa only [fun_blocktype, fun_type, AFrame.toFrame, proj_uN_0,
        getElem!_pos f.module.TYPES i hi] using heq

theorem typed_block_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frame_typed_wf hf
    obtain ⟨C, first, args, inputs, outputs, bindings, _, hop, hsplit, hargs, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop with
    | block _ _ _ ins outs hbt hbody hC hi hnew =>
      have hbt' := block_type_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
      have hlen := results_typed_length hargs
      have htypes := results_type_of_typed hargs
      have hheight : f.vals.length - inputs.length = first.length := by rw [hsplit, List.length_append, hlen]; omega
      have hbound : inputs.length ≤ f.vals.length := by rw [hsplit, List.length_append, hlen]; omega
      have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
        rw [hheight, hsplit, List.drop_left]
        exact htypes
      have result := block_simulation s ambient f rest after body first args bt inputs outputs
        typed.store typed.ambient hw hl hfirst (results_typed_wf hargs)
        (fun i hm => hc i (by simp [hm])) (frames_typed_wf hr) heights hi
        (block_type_spec s f bt _ hbt') hlen
      have hnext : next = ⟨s, ambient,
          { f with code := body, labels := ⟨outputs, outputs, [], first.length, after⟩ :: f.labels } :: rest, []⟩ := by
        simpa [astep, enterLabel, hbt', hbound, htail, hheight, hsplit, hlen, htypes, advance] using step.symm
      rw [hnext]
      apply NextSim.single
      simpa only [← hsplit] using result

theorem typed_loop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, _, hc⟩ := frame_typed_wf hf
    obtain ⟨C, first, args, inputs, outputs, bindings, _, hop, hsplit, hargs, hfirst, heights⟩ := frame_typed_operands_bounds hf
    cases hop with
    | loop _ _ _ ins outs hbt hbody hC hi hnew =>
      have hbt' := block_type_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
      have hlen := results_typed_length hargs
      have htypes := results_type_of_typed hargs
      have hheight : f.vals.length - inputs.length = first.length := by rw [hsplit, List.length_append, hlen]; omega
      have hbound : inputs.length ≤ f.vals.length := by rw [hsplit, List.length_append, hlen]; omega
      have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
        rw [hheight, hsplit, List.drop_left]
        exact htypes
      have result := loop_simulation s ambient f rest after body first args bt inputs outputs
        typed.store typed.ambient hw hl hfirst (results_typed_wf hargs)
        (fun i hm => hc i (by simp [hm])) (frames_typed_wf hr) heights hi
        (block_type_spec s f bt _ hbt') hlen
      have hnext : next = ⟨s, ambient,
          { f with code := body, labels := ⟨inputs, outputs, [.LOOP bt body], first.length, after⟩ :: f.labels } :: rest, []⟩ := by
        simpa [astep, enterLabel, hbt', hbound, htail, hheight, hsplit, hlen, htypes, advance] using step.symm
      rw [hnext]
      apply NextSim.single
      simpa only [← hsplit] using result

end Itasca.Runtime.SourceMachine

end
