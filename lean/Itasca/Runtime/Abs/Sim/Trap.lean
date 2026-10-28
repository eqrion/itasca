import Itasca.Runtime.Abs.Sim.Trace

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem wf_trap : Forall wf_admininstr [admininstr.TRAP] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact .admininstr_case_73

theorem trap_values (s : store) (f : frame) (values : List val) (after : List admininstr)
    (hs : wf_store s) (hf : wf_frame f)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    ∃ n, StepsHN n ⟨⟨s, f⟩, vals values ++ ([.TRAP] ++ after)⟩ [] ⟨⟨s, f⟩, [.TRAP]⟩ := by
  have hw := wf_config_make hs hf wf_trap
  by_cases h : values ≠ [] ∨ after ≠ []
  · have before := wf_config_make hs hf (forall_append (wf_vals hv) (forall_append wf_trap ha))
    have step : StepH ⟨⟨s, f⟩, vals values ++ ([.TRAP] ++ after)⟩ [] ⟨⟨s, f⟩, [.TRAP]⟩ :=
      .step (.pure _ _ _ (.trap_vals values after h hv ha .admininstr_case_73) before hw)
    exact ⟨1, by simpa only [List.nil_append] using StepsHN.cons step (StepsHN.refl hw)⟩
  · have hv : values = [] := by tauto
    have ha : after = [] := by tauto
    subst values
    subst after
    exact ⟨0, by simpa [vals] using StepsHN.refl hw⟩

theorem trap_label (s : store) (f : frame) (arity : Nat) (cont : List instr)
    (hs : wf_store s) (hf : wf_frame f) (hc : Forall wf_instr cont) :
    StepH ⟨⟨s, f⟩, [.LABEL_ arity cont [.TRAP]]⟩ [] ⟨⟨s, f⟩, [.TRAP]⟩ := by
  have hw := wf_config_make hs hf wf_trap
  have hl : wf_admininstr (.LABEL_ arity cont [.TRAP]) := .admininstr_case_71 _ _ _ hc wf_trap
  exact .step (.pure _ _ _ (.trap_label arity cont hl .admininstr_case_73)
    (wf_config_label arity hw hc) hw)

/-- Each label is removed by the generated trap rule after its inner operands
and continuation have been discarded. -/
theorem trap_labels (s : store) (f : frame) (labels : List Label)
    (values : List val) (after : List admininstr)
    (hs : wf_store s) (hf : wf_frame f) (hl : LabelsWf labels)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    ∃ n, StepsHN n ⟨⟨s, f⟩, decodeLabels labels values ([.TRAP] ++ after)⟩ []
      ⟨⟨s, f⟩, [.TRAP]⟩ := by
  induction labels generalizing values after with
  | nil => exact trap_values s f values after hs hf hv ha
  | cons label labels ih =>
    have hc := hl label (by simp)
    have hr : LabelsWf labels := fun l hm => hl l (by simp [hm])
    have ht : Forall wf_val (values.take label.height) := fun v hm => hv v (List.mem_of_mem_take hm)
    obtain ⟨n, inner⟩ := trap_values s f (values.drop label.height) after hs hf
      (fun v hm => hv v (List.mem_of_mem_drop hm)) ha
    have first := stepsHN_decodeLabels
      (stepsHN_instrs (stepsHN_label inner label.arity label.cont hc.1) []
        (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hc.2))
      labels (values.take label.height) hr ht
    have second := stepH_decodeLabels
      (stepH_instrs (trap_label s f label.arity label.cont hs hf hc.1) []
        (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hc.2))
      labels (values.take label.height) hr ht
    obtain ⟨m, tail⟩ := ih (values.take label.height) (label.after.map admininstr_instr) hr ht (wf_instrs hc.2)
    have rest := StepsHN.cons second tail
    have all := first.trans rest
    exact ⟨n + (m + 1), by simpa [decodeLabels, instrContext, Itasca.Runtime.Spec.labelContext, vals] using all⟩

theorem trap_frame (s : store) (outer inner : frame) (arity : Nat)
    (hs : wf_store s) (ho : wf_frame outer) (hi : wf_frame inner) :
    StepH ⟨⟨s, outer⟩, [.FRAME_ arity inner [.TRAP]]⟩ [] ⟨⟨s, outer⟩, [.TRAP]⟩ := by
  have hw := wf_config_make hs ho wf_trap
  have hiw := wf_config_make hs hi wf_trap
  have hf : wf_admininstr (.FRAME_ arity inner [.TRAP]) := .admininstr_case_72 _ _ _ hi wf_trap
  exact .step (.pure _ _ _ (.trap_frame arity inner hf .admininstr_case_73)
    (wf_config_frame arity hiw ho) hw)

/-- Trap unwinding crosses every suspended caller, with its own frame context. -/
theorem trap_frames (s : store) (ambient : frame) (frames : List AFrame)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    ∃ n, StepsHN n ⟨⟨s, ambient⟩, decodeFrames frames [.TRAP]⟩ [] ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  induction frames with
  | nil => exact ⟨0, .refl (wf_config_make hs ha wf_trap)⟩
  | cons f rest ih =>
    obtain ⟨hw, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun f hm => hf f (by simp [hm])
    obtain ⟨n, inner⟩ := trap_labels s f.toFrame f.labels f.vals (f.code.map admininstr_instr)
      hs hw hl hv (wf_instrs hc)
    have first := stepsHN_decodeFrames ambient rest
      (stepsHN_frame inner f.arity (activeFrame ambient rest) (activeFrame_wf ha hr)) ha hr
    have second := stepH_decodeFrames ambient rest
      (trap_frame s (activeFrame ambient rest) f.toFrame f.arity hs (activeFrame_wf ha hr) hw) ha hr
    obtain ⟨m, tail⟩ := ih hr
    exact ⟨n + (m + 1), by
      simpa [decodeFrames, frameContext] using first.trans (StepsHN.cons second tail)⟩

/-- An unreachable instruction takes a positive number of specification steps
to the terminal trap, even inside arbitrarily nested labels and calls. -/
theorem unreachable_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, [.UNREACHABLE]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_1)
  have ht := wf_config_make hs hf wf_trap
  have step : StepH ⟨⟨s, f.toFrame⟩, [.UNREACHABLE]⟩ [] ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    .step (.pure _ _ _ (.unreachable .admininstr_case_1 .admininstr_case_73) hw ht)
  have lifted := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels f.vals hl hv) ha hr
  have hframes : Forall FrameWf ({ f with code := after } :: rest) := by
    intro frame hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hf, hl, hv, hc⟩
    · exact hr frame hm
  obtain ⟨n, tail⟩ := trap_frames s ambient ({ f with code := after } :: rest) hs ha hframes
  refine ⟨n + 1, by omega, ?_⟩
  simpa [decode, decodeFrames, vals, instrContext, AFrame.arity, AFrame.toFrame, admininstr_instr] using
    StepsHN.cons lifted tail

end Itasca.Runtime.Abs
