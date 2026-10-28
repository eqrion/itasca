import Itasca.Runtime.Abs.Sim.Int

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

/-- The abstract conditional selects the same block as the generated rule. -/
theorem if_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (bits : Nat) (bt : blocktype) (yes no : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : bits < 2 ^ integerWidth .I32) (hi : wf_instr (.IFELSE bt yes no)) :
    StepH (decode ⟨s, ambient,
      { f with code := .IFELSE bt yes no :: after, vals := baseValues ++ [integerVal .I32 bits] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := baseValues } :: rest, []⟩) := by
  have hblock : wf_instr (.BLOCK bt (if bits = 0 then no else yes)) := by
    cases hi with
    | instr_case_6 _ _ _ hbt hy hn =>
      apply wf_instr.instr_case_4 _ _ hbt
      split <;> assumption
  have hp : Step_pure [admininstr_val (integerVal .I32 bits), .IFELSE bt yes no]
      [.BLOCK bt (if bits = 0 then no else yes)] := by
    by_cases hz : bits = 0
    · simpa only [integerVal, admininstr_val, numtype_Inn, hz, ite_true] using Step_pure.if_false (.mk_num__0 .I32 (.mk_uN bits)) bt yes no
        (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
        (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
        (wf_admininstr_instr (i := .BLOCK bt no) (by simpa only [hz, ite_true] using hblock))
    · simpa only [integerVal, admininstr_val, numtype_Inn, hz, ite_false] using Step_pure.if_true (.mk_num__0 .I32 (.mk_uN bits)) bt yes no
        (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
        (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
        (wf_admininstr_instr (i := .BLOCK bt yes) (by simpa only [hz, ite_false] using hblock))
  simpa only [List.append_nil, List.singleton_append] using
    pure_code_simulation s ambient f rest (.IFELSE bt yes no) [.BLOCK bt (if bits = 0 then no else yes)] after
      baseValues [integerVal .I32 bits] [] hs ha hf hl hv hc hr heights
      (by intro value h; simp only [List.mem_singleton] at h; subst value; exact integer_val_wf .I32 bits hb)
      (forall_nil _) hi
      (by intro op h; simp only [List.mem_singleton] at h; subst op; exact hblock) hp

theorem br_if_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (bits index : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : bits < 2 ^ integerWidth .I32) (hi : index < 2 ^ 32) :
    StepH (decode ⟨s, ambient,
      { f with code := .BR_IF (.mk_uN index) :: after, vals := baseValues ++ [integerVal .I32 bits] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := if bits = 0 then after else .BR (.mk_uN index) :: after, vals := baseValues } :: rest, []⟩) := by
  have hidx := integer_uN_wf .I32 index hi
  have hi' : wf_instr (.BR_IF (.mk_uN index)) := .instr_case_8 _ hidx
  have hbr : wf_instr (.BR (.mk_uN index)) := .instr_case_7 _ hidx
  let replacement : List instr := if bits = 0 then [] else [.BR (.mk_uN index)]
  have hp : Step_pure [admininstr_val (integerVal .I32 bits), .BR_IF (.mk_uN index)]
      (replacement.map admininstr_instr) := by
    by_cases hz : bits = 0
    · simpa only [integerVal, admininstr_val, numtype_Inn, replacement, hz, ite_true, List.map_nil] using
        Step_pure.br_if_false (.mk_num__0 .I32 (.mk_uN bits)) (.mk_uN index)
          (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi')
    · simpa only [integerVal, admininstr_val, numtype_Inn, replacement, hz, ite_false, List.map_cons, List.map_nil, admininstr_instr] using
        Step_pure.br_if_true (.mk_num__0 .I32 (.mk_uN bits)) (.mk_uN index)
          (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi') (wf_admininstr_instr hbr)
  have hrepl : Forall wf_instr replacement := by
    intro op h
    dsimp [replacement] at h
    split at h
    · contradiction
    · simp only [List.mem_singleton] at h; subst op; exact hbr
  have h := pure_code_simulation s ambient f rest (.BR_IF (.mk_uN index)) replacement after
      baseValues [integerVal .I32 bits] [] hs ha hf hl hv hc hr heights
      (by intro value h; simp only [List.mem_singleton] at h; subst value; exact integer_val_wf .I32 bits hb)
      (forall_nil _) hi' hrepl hp
  by_cases hz : bits = 0 <;> simpa only [integerVal, admininstr_val, numtype_Inn, replacement, hz, ite_true, ite_false,
    List.append_nil, List.nil_append, List.singleton_append] using h


/-- Entering a block installs the generated label with the exact saved stack
height, parameter values, and continuation. -/
theorem block_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after body : List instr) (baseValues args : List val)
    (bt : blocktype) (params results : List valtype)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hargs : Forall wf_val args)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hiOp : wf_instr (.BLOCK bt body))
    (hbt : fun_blocktype ⟨s, f.toFrame⟩ bt = ⟨.mk_list params, .mk_list results⟩)
    (hlen : args.length = params.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .BLOCK bt body :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := body, vals := baseValues ++ args, labels := ⟨results, results, [], baseValues.length, after⟩ :: f.labels } :: rest, []⟩) := by
  have hbody : Forall wf_instr body := by cases hiOp; assumption
  have hlabel : wf_admininstr (.LABEL_ results.length [] (vals args ++ body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (forall_nil _) (forall_append (wf_vals hargs) (wf_instrs hbody))
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, vals args ++ [.BLOCK bt body]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr hiOp))
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ results.length [] (vals args ++ body.map admininstr_instr)]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hlabel)
  have read := Step_read.block ⟨s, f.toFrame⟩ args.length args bt body results.length params results
    hbt hsource hlabel rfl hlen rfl
  have step : StepH ⟨⟨s, f.toFrame⟩, vals args ++ [.BLOCK bt body]⟩ []
      ⟨⟨s, f.toFrame⟩, [.LABEL_ results.length [] (vals args ++ body.map admininstr_instr)]⟩ :=
    .step (.read _ _ _ read hsource htarget)
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeLabels, Label.arity, instrContext, vals, List.append_assoc, AFrame.arity,
    AFrame.toFrame, admininstr_instr, hlen] using h₃

/-- Entering a loop installs the generated label with the exact saved stack
height, parameter values, and continuation. -/
theorem loop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after body : List instr) (baseValues args : List val)
    (bt : blocktype) (params results : List valtype)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hargs : Forall wf_val args)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hiOp : wf_instr (.LOOP bt body))
    (hbt : fun_blocktype ⟨s, f.toFrame⟩ bt = ⟨.mk_list params, .mk_list results⟩)
    (hlen : args.length = params.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .LOOP bt body :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := body, vals := baseValues ++ args, labels := ⟨params, results, [.LOOP bt body], baseValues.length, after⟩ :: f.labels } :: rest, []⟩) := by
  have hbody : Forall wf_instr body := by cases hiOp; assumption
  have hlabel : wf_admininstr (.LABEL_ params.length [.LOOP bt body] (vals args ++ body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hiOp) (forall_append (wf_vals hargs) (wf_instrs hbody))
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, vals args ++ [.LOOP bt body]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr hiOp))
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ params.length [.LOOP bt body] (vals args ++ body.map admininstr_instr)]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hlabel)
  have read := Step_read.loop ⟨s, f.toFrame⟩ params.length args bt body params results.length results
    hbt hsource hlabel hlen.symm rfl rfl
  have step : StepH ⟨⟨s, f.toFrame⟩, vals args ++ [.LOOP bt body]⟩ []
      ⟨⟨s, f.toFrame⟩, [.LABEL_ params.length [.LOOP bt body] (vals args ++ body.map admininstr_instr)]⟩ :=
    .step (.read _ _ _ read hsource htarget)
  have h₁ := stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := stepH_decodeLabels h₁ f.labels baseValues hl hv
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeLabels, Label.arity, instrContext, vals, List.append_assoc, AFrame.arity,
    AFrame.toFrame, admininstr_instr, hlen] using h₃

/-- Completing a label removes exactly that administrative wrapper, preserving
the saved prefix and the values produced by its body. -/
theorem label_exit_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf (label :: labels)) (hv : Forall wf_val f.vals)
    (hr : Forall FrameWf rest)
    (hheight : label.height ≤ f.vals.length)
    (heights : ∀ outer ∈ labels, outer.height ≤ label.height) :
    StepH (decode ⟨s, ambient,
      { f with code := [], labels := label :: labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := label.after, labels := labels } :: rest, []⟩) := by
  have hlabel := hl label (by simp)
  have htail : LabelsWf labels := fun l hm => hl l (by simp [hm])
  have hbefore : Forall wf_val (f.vals.take label.height) := fun v hm => hv v (List.mem_of_mem_take hm)
  have hafter : Forall wf_val (f.vals.drop label.height) := fun v hm => hv v (List.mem_of_mem_drop hm)
  have hwrap : wf_admininstr (.LABEL_ label.arity label.cont (vals (f.vals.drop label.height))) :=
    .admininstr_case_71 _ _ _ hlabel.1 (wf_vals hafter)
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont (vals (f.vals.drop label.height))]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget := wf_config_vals hs hf hafter
  have step : StepH ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont (vals (f.vals.drop label.height))]⟩ []
      ⟨⟨s, f.toFrame⟩, vals (f.vals.drop label.height)⟩ :=
    .step (.pure _ _ _ (.label_vals _ _ _ hwrap) hsource htarget)
  have h₁ := stepH_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := stepH_decodeLabels h₁ labels (f.vals.take label.height) htail hbefore
  have h₃ := stepH_active ambient rest f.arity h₂ ha hr
  have hm := decodeLabels_move_values labels (f.vals.take label.height) (f.vals.drop label.height)
    (label.after.map admininstr_instr) (by
      intro l hl
      simpa only [List.length_take, Nat.min_eq_left hheight] using heights l hl)
  rw [List.take_append_drop] at hm
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [hm]
  simpa [decodeLabels, instrContext, vals, AFrame.arity, AFrame.toFrame] using h₃

end Itasca.Runtime.Abs
