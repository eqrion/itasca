import Itasca.Runtime.Abs.Sim.Basic
import Itasca.Runtime.Abs.Typing
import Itasca.Runtime.Spec.Counted

namespace Itasca.Runtime.Abs
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
      exact .admininstr_case_43 _ (integer_uN_wf .I32 index hi32))
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
      · exact .admininstr_case_44 _ (integer_uN_wf .I32 index hi32))
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
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
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
  have hi := integer_uN_wf .I32 index hi32
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
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  have expanded : StepH (decode ⟨s, ambient,
      { f with code := .LOCAL_TEE (.mk_uN index) :: after, vals := baseValues ++ [value] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := .LOCAL_SET (.mk_uN index) :: after, vals := (baseValues ++ [value]) ++ [value] } :: rest, []⟩) := by
    simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
      AFrame.toFrame, AFrame.arity]
    rw [decodeLabels_move_values _ _ _ _ heights]
    rw [List.append_assoc, decodeLabels_move_values _ _ _ _ heights]
    simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr] using h₃
  have valuesWf : Forall wf_val (baseValues ++ [value]) := forall_append hv (by
    intro x hx'; simp only [List.mem_singleton] at hx'; subst x; exact hx)
  have heights' : ∀ label ∈ f.labels, label.height ≤ (baseValues ++ [value]).length := by
    intro label h; have hh := heights label h; simp only [List.length_append, List.length_singleton]; omega
  have write := local_set_simulation s ambient f rest after (baseValues ++ [value]) value index
    hs ha hf hl valuesWf hx hc hr heights' hi32
  exact .cons expanded (.cons write (.refl (stepH_wf write).2))

end Itasca.Runtime.Abs
