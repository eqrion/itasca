import Itasca.Runtime.Abs.Numeric.Binary
import Itasca.Runtime.Abs.Sim.Trap

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem binary_pure (ty : Inn) (op : binop_Inn)
    (a b result : BitVec (sizenn (numtype_Inn ty)))
    (success : binary ty op a b = some result) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))]
      [admininstr_val (integerVal ty result.toNat)] := by
  apply Step_pure.binop_val (numtype_Inn ty) (.mk_num__0 ty (.mk_uN a.toNat))
    (.mk_num__0 ty (.mk_uN b.toNat)) (.mk_binop__0 ty op)
    (.mk_num__0 ty (.mk_uN result.toNat)) (some [.mk_num__0 ty (.mk_uN result.toNat)])
  · simpa only [success, binaryNumbers] using binary_relation ty op a b
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty a))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty b))
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty result))

theorem binary_trap_pure (ty : Inn) (op : binop_Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) (trap : binary ty op a b = none) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))] [.TRAP] := by
  apply Step_pure.binop_trap (numtype_Inn ty) (.mk_num__0 ty (.mk_uN a.toNat))
    (.mk_num__0 ty (.mk_uN b.toNat)) (.mk_binop__0 ty op) (some [])
  · simpa only [trap, binaryNumbers] using binary_relation ty op a b
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty a))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty b))
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_0 _ _ _ rfl))
  · exact .admininstr_case_73

/-- Numeric traps unwind all labels and suspended calls in finitely many real
source reductions. The operands remain bounded source words throughout. -/
theorem binary_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (op : binop_Inn) (a b : BitVec (sizenn (numtype_Inn ty)))
    (trap : binary ty op a b = none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient,
        { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after, vals := baseValues ++ [integerVal ty a.toNat, integerVal ty b.toNat] } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  let operands := [integerVal ty a.toNat, integerVal ty b.toNat]
  have operandsWf : Forall wf_val operands := by
    intro value h; simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact integer_val_wf ty _ (word_bound ty a)
    · exact integer_val_wf ty _ (word_bound ty b)
  have instructionWf : wf_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op)) :=
    .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)
  have before : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))]⟩ := wf_config_make hs hf (forall_append (wf_vals operandsWf)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr instructionWf))
  have step : StepH ⟨⟨s, f.toFrame⟩, vals operands ++
      [admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))]⟩ []
      ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    .step (.pure _ _ _ (binary_trap_pure ty op a b trap) before (wf_config_make hs hf wf_trap))
  have lifted := stepH_active ambient rest f.arity
    (stepH_decodeLabels (stepH_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels baseValues hl hv) ha hr
  have frameWf : Forall FrameWf ({ f with code := after, vals := baseValues } :: rest) := by
    intro frame hm; simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hf, hl, hv, hc⟩
    · exact hr frame hm
  obtain ⟨n, tail⟩ := trap_frames s ambient ({ f with code := after, vals := baseValues } :: rest) hs ha frameWf
  refine ⟨n + 1, by omega, ?_⟩
  have all := StepsHN.cons lifted tail
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [decodeFrames, operands, vals, instrContext, AFrame.toFrame, AFrame.arity, List.append_assoc] using all
end Itasca.Runtime.Abs.Numeric
