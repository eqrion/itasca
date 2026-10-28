import Itasca.Runtime.Abs.Sim.Context
import Itasca.Runtime.Abs.Measure

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- Constants are already values in SpecTec's administrative instruction syntax.
Moving one into the flat stack is therefore an exact decoding equality. -/
theorem decode_const (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (ty : numtype) (value : num_) (after : List instr)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length) :
    decode ⟨s, ambient, { f with code := .CONST ty value :: after } :: rest, []⟩ =
    decode ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [.CONST ty value] } :: rest, []⟩ := by
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append,
    AFrame.toFrame, List.map_cons, admininstr_instr]
  rw [decodeLabels_move_values _ _ _ _ heights]
  rfl

/-- Nop is a real specification step, under arbitrarily many labels and callers. -/
theorem nop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest) :
    StepH (decode ⟨s, ambient, { f with code := .NOP :: after } :: rest, []⟩) []
      (decode ⟨s, ambient, { f with code := after } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, [.NOP]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_0)
  have hw' : wf_config ⟨⟨s, f.toFrame⟩, []⟩ := wf_config_make hs hf (forall_nil _)
  have h : StepH ⟨⟨s, f.toFrame⟩, [.NOP]⟩ [] ⟨⟨s, f.toFrame⟩, []⟩ :=
    .step (.pure _ _ _ (.nop .admininstr_case_0) hw hw')
  have h₁ := stepH_instrs h [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels f.vals hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simpa [decode, decodeFrames, instrContext, vals, AFrame.toFrame, AFrame.arity, admininstr_instr] using h₃

/-- Reuse a generated pure reduction under the flat operand stack and every
nested execution context. The consumed operands must lie above label heights. -/
theorem pure_stack_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : Forall wf_val consumed) (hp : Forall wf_val produced)
    (hi : wf_instr instruction)
    (h : Step_pure (vals consumed ++ [admininstr_instr instruction]) (vals produced)) :
    StepH (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hb)
      (by intro ai hai; simp only [List.mem_singleton] at hai; subst ai; exact wf_admininstr_instr hi))
  have hw' := wf_config_vals hs hf hp
  have step : StepH ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced⟩ := .step (.pure _ _ _ h hw hw')
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

/-- Drop discards the top value and leaves the remaining operand stack intact. -/
theorem drop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val) (value : val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hx : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .DROP :: after, vals := baseValues ++ [value] } :: rest, []⟩) []
      (decode ⟨s, ambient, { f with code := after, vals := baseValues } :: rest, []⟩) := by
  simpa using pure_stack_simulation s ambient f rest .DROP after baseValues [value] []
    hs ha hf hl hv hc hr heights
    (by intro x h; simp only [List.mem_singleton] at h; subst x; exact hx)
    (forall_nil _) .instr_case_2 (.drop value hx .admininstr_case_2)

theorem stack_step_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (ha : wf_frame ambient)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : StepH ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced⟩) :
    StepH (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

/-- Lift a pure source rewrite that replaces the current instruction by a
short instruction sequence, possibly consuming or producing stack values. -/
theorem pure_code_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (replacement after : List instr)
    (baseValues consumed produced : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : Forall wf_val consumed) (hp : Forall wf_val produced)
    (hi : wf_instr instruction) (hrepl : Forall wf_instr replacement)
    (h : Step_pure (vals consumed ++ [admininstr_instr instruction])
      (vals produced ++ replacement.map admininstr_instr)) :
    StepH (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := replacement ++ after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hb)
      (by intro ai hai; simp only [List.mem_singleton] at hai; subst ai; exact wf_admininstr_instr hi))
  have hw' : wf_config ⟨⟨s, f.toFrame⟩, vals produced ++ replacement.map admininstr_instr⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hp) (wf_instrs hrepl))
  have step : StepH ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced ++ replacement.map admininstr_instr⟩ := .step (.pure _ _ _ h hw hw')
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, List.map_append]
  rw [decodeLabels_move_values _ _ _ _ heights, decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

end Itasca.Runtime.Abs
