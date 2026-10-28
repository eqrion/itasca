import Exec.Abs.Sim.Branch
import Exec.Abs.Preservation

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- Appending a callee's results to its suspended caller agrees with inserting
those values into the decoded frame context. Saved prefixes already exist. -/
theorem decode_resume (s : store) (ambient : frame) (caller : AFrame)
    (rest : List AFrame) (values : List val) (heights : FrameHeights caller) :
    decode ⟨s, ambient, { caller with vals := caller.vals ++ values } :: rest, []⟩ =
      ⟨⟨s, ambient⟩, decodeFrames (caller :: rest) (vals values)⟩ := by
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
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
    wf_config_make hs (activeFrame_wf ha hr)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget := wf_config_vals hs (activeFrame_wf ha hr) hv
  have step : StepH ⟨⟨s, activeFrame ambient rest⟩, [.FRAME_ f.arity f.toFrame (vals f.vals)]⟩ []
      ⟨⟨s, activeFrame ambient rest⟩, vals f.vals⟩ :=
    .step (.pure _ _ _ (.frame_vals _ _ _ hwrap arity) hsource htarget)
  simpa [decode, decodeFrames, decodeLabels, vals, AFrame.toFrame, AFrame.arity] using
    stepH_decodeFrames ambient rest step ha hr

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
    wf_config_make hs (activeFrame_wf ha hr)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget := wf_config_vals hs (activeFrame_wf ha hr) hv
  have step : StepH ⟨⟨s, activeFrame ambient rest⟩, [.FRAME_ f.arity f.toFrame redex]⟩ []
      ⟨⟨s, activeFrame ambient rest⟩, vals results⟩ :=
    .step (.pure _ _ _ (.return_frame _ _ _ _ _ hwrap arity) hsource htarget)
  simpa [decode, decodeFrames, decodeLabels, redex, vals, List.map_append,
    List.append_assoc, admininstr_instr, AFrame.toFrame, AFrame.arity] using
    stepH_decodeFrames ambient rest step ha hr

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
  have h₁ := stepH_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := stepH_decodeLabels h₁ labels saved htail hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    List.map_append, AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
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
      StepsHN.cons step (StepsHN.refl (stepH_wf step).2)
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
    have count := resultsTyped_length results
    simp only [List.length_drop] at count
    have bound : f.arity ≤ f.vals.length := by unfold AFrame.arity; omega
    have heights : FrameHeights f := typed.heights { f with code := .RETURN :: after } (by simp)
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      have result := return_simulation s ambient f rest f.labels after typed.store typed.ambient hw
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

theorem typed_frame_end_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ = .next next) :
    StepH (decode ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    have values := frame_end_typed hf
    have count := resultsTyped_length values
    have arity : f.arity = f.vals.length := count.symm
    have result := frame_end_simulation s ambient f rest typed.store typed.ambient
      (frameTyped_wf hf).1 (resultsTyped_wf values) (framesTyped_wf hr) arity
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

end Itasca.Runtime.Abs
