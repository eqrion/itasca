import Exec.Abs.Sim.Local
import Exec.Abs.Sim.NeutralDecode
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_local_tee_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (value : val) (index : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hx : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hi32 : index < 2 ^ 32) :
    ChosenStepsN choices occurrence 2 (decode ⟨s, ambient,
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
  have first := chosen_neutral_simulation admissible vector occurrence expanded
    (by simp only [List.map_cons,admininstr_instr,neutralActive])
  have second := chosen_neutral_simulation admissible vector (occurrence+1) write
    (by simp only [List.map_cons,admininstr_instr,neutralActive])
  exact .cons first (.cons second (.refl (occurrence+1+1) (second.wf admissible).2))

end Exec.Abs
