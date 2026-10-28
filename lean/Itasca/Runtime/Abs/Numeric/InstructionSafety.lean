import Itasca.Runtime.Abs.Numeric.Instruction

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem Instruction.frame_preservation (op : Instruction)
    {s : store} {f : AFrame} {after : List instr} {front : List val}
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output))) (hs : wf_store s)
    (typed : FrameTyped s { f with code := op.source :: after, vals := front ++ op.operands a b } []) :
    FrameTyped s { f with code := after, vals := front ++ [integerVal op.output result.toNat] } [] := by
  cases op with
  | binary ty binop => exact integer_binop_frame_preservation hs (word_bound _ _) typed
  | unary ty unop => exact unary_frame_preservation hs (word_bound _ _) typed
  | compare ty relop => exact integer_relop_frame_preservation hs (word_bound _ _) typed
  | eqz ty => exact integer_testop_frame_preservation hs (word_bound _ _) typed
  | conversion conv => exact conversion_frame_preservation hs (word_bound _ _) typed

theorem Instruction.simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    StepH (decode ⟨s, ambient,
      { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := front ++ [integerVal op.output result.toNat] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after front _ _ hs ha hf hl hv hc hr heights
  · exact op.operands_wf a b
  · intro value h; simp only [List.mem_singleton] at h; subst value
    exact integer_val_wf _ _ (word_bound _ _)
  · exact op.source_wf
  · exact op.pure_success a b result success

theorem Instruction.trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b : BitVec (sizenn (numtype_Inn op.input)))
    (trap : op.apply a b = none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient,
        { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  cases op with
  | binary ty binop => exact binary_trap_simulation s ambient f rest after front ty binop a b trap hs ha hf hl hv hc hr heights
  | unary | compare | eqz | conversion => simp only [apply, Option.some_ne_none] at trap
end Itasca.Runtime.Abs.Numeric
