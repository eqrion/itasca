import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Sim.Typed
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Runtime.SourceMachine.Sim.Trap

/-!
Floating-point source-machine transition from typed operands through preservation, simulation and positivity. Descriptor and result selection remain independently available.
-/

/-! ## Operands -/

section

namespace Itasca.Runtime.SourceMachine.Float
open SpecExt Itasca.Runtime.Spec SpecExt.Builtins SpecExt.Builtins.Float

theorem number_encoding (ty : numtype) (number : num_) (valid : wf_num_ ty number) :
    ∃ bits, number = numberOfBits ty bits ∧ bits < 2^sizenn ty := by
  cases valid with
  | num__case_0 ity value _ bounded same =>
    subst ty
    cases value with
    | mk_uN bits =>
      refine ⟨bits, (number_of_bits_integer ity bits).symm, ?_⟩
      cases bounded with
      | uN_case_0 _ limit =>
        cases ity <;> norm_num [sizenn, numtype_Inn, valtype_numtype, valtype_Inn, size] at limit ⊢ <;> omega
  | num__case_1 fty value valid same =>
    subst ty
    obtain ⟨bits, bound, encoding⟩ := float_encoding fty value valid
    refine ⟨bits, ?_, bound⟩
    rw [number_of_bits_float, encoding]

theorem numeric_val_encoding {s : store} {ty : numtype} {value : val}
    (typed : Val_ok s value (valtype_numtype ty)) :
    ∃ bits, value = .CONST ty (numberOfBits ty bits) ∧ bits < 2^sizenn ty := by
  have valid := val_ok_wf typed
  have typeEq := value_type_of_typed typed
  cases valid with
  | val_case_0 nt number valid =>
    have same : nt = ty := by cases nt <;> cases ty <;> simp_all [valueType, valtype_numtype]
    subst nt
    obtain ⟨bits, rfl, bound⟩ := number_encoding ty number valid
    exact ⟨bits, rfl, bound⟩
  | val_case_1 vt bits _ => cases ty <;> simp_all [valueType, valtype_numtype]
  | val_case_2 rt => cases ty <;> cases rt <;> simp_all [valueType, valtype_numtype, valtype_reftype]
  | val_case_3 address => cases ty <;> simp_all [valueType, valtype_numtype]
  | val_case_4 address => cases ty <;> simp_all [valueType, valtype_numtype]

theorem Instruction.typed_operands (op : Instruction) {s : store} {f : AFrame}
    {after : List instr} (typed : FrameTyped s { f with code := op.source :: after } []) :
    ∃ front a b, f.vals = front ++ op.operands a b ∧ a < 2^sizenn op.input ∧ b < 2^sizenn op.input ∧
      Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C, front, operands, ins, outs, _, _, step, split, typedOperands, frontWf, heights⟩ := frame_typed_operands_bounds typed
  cases op <;> cases step
  all_goals first
    | cases typedOperands with
      | cons first rest =>
        cases rest with
        | cons second last =>
          cases last
          obtain ⟨a, rfl, firstBound⟩ := numeric_val_encoding first
          obtain ⟨b, rfl, secondBound⟩ := numeric_val_encoding second
          refine ⟨front, a, b, ?_, firstBound, secondBound, frontWf, heights⟩
          simpa [Instruction.operands, Instruction.arity, Instruction.input] using split
    | cases typedOperands with
      | cons first rest =>
        cases rest
        obtain ⟨a, rfl, firstBound⟩ := numeric_val_encoding first
        refine ⟨front, a, a, ?_, firstBound, firstBound, frontWf, heights⟩
        simpa [Instruction.operands, Instruction.arity, Instruction.input] using split

end Itasca.Runtime.SourceMachine.Float

end

/-! ## Preservation -/

section

namespace Itasca.Runtime.SourceMachine.Float
open SpecExt Itasca.Runtime.Spec SpecExt.Builtins SpecExt.Builtins.Float

theorem Instruction.source_signature_inv (op : Instruction) {C : context} {signature : functype}
    (typed : Instr_ok C op.source signature) : signature = op.signature := by
  cases op <;> cases typed <;> rfl

theorem Instruction.operands_types (op : Instruction) (a b : Nat) :
    (op.operands a b).map valueType = List.replicate op.arity (valtype_numtype op.input) := by
  cases op <;> rfl

theorem Instruction.frame_preservation (op : Instruction) {s : store} {f : AFrame} {after : List instr}
    (front : List val) (a b bits : Nat) (storeWf : wf_store s)
    (bound : bits < 2^sizenn op.output)
    (typed : FrameTyped s { f with code := op.source :: after, vals := front ++ op.operands a b } []) :
    FrameTyped s { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code contextWf =>
    simp only [List.append_nil] at code
    obtain ⟨prefixTypes, ins, outs, instruction, stack, continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ op.operands a b)) code
    have signature := op.source_signature_inv instruction
    simp only [Instruction.signature, functype.mk_functype.injEq, list.mk_list.injEq] at signature
    rcases signature with ⟨rfl, rfl⟩
    simp only [List.map_append, operands_types, List.append_cancel_right_eq] at stack
    have frontTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    have resultTyped := number_of_bits_typed s storeWf op.output bits bound
    apply FrameTyped.mk (f := { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] }) C
      bindings localTypes locals ?_ returns ?_ contextWf
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, valueType] using
        List.rel_append frontTyped (List.Forall₂.cons resultTyped List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil, valueType, stack] using continuation

end Itasca.Runtime.SourceMachine.Float

end

/-! ## Simulation -/

section

namespace Itasca.Runtime.SourceMachine.Float
open SpecExt Itasca.Runtime.Spec

theorem Instruction.simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b bits : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (effect : op.Result a b (some bits))
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    StepH (decode ⟨s, ambient,
      { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after front _ _ hs ha hf hl hv hc hr heights
  · exact op.operands_wf a b first second
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact .val_case_0 _ _ (number_of_bits_wf _ _ effect.1)
  · exact op.source_wf
  · exact effect.2

theorem Instruction.trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (op : Instruction) (a b : Nat)
    (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
    (trap : op.Result a b none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient,
        { f with code := op.source :: after, vals := baseValues ++ op.operands a b } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  let operands := op.operands a b
  have operandsWf : Forall wf_val operands := op.operands_wf a b first second
  have instructionWf : wf_instr op.source := op.source_wf
  have before : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [admininstr_instr op.source]⟩ := wf_config_make hs hf (forall_append (wf_vals operandsWf)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr instructionWf))
  have step : StepH ⟨⟨s, f.toFrame⟩, vals operands ++
      [admininstr_instr op.source]⟩ []
      ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    .step (.pure _ _ _ trap before (wf_config_make hs hf wf_trap))
  have lifted := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
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
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeFrames, operands, vals, instrContext, AFrame.toFrame, AFrame.arity, List.append_assoc] using all

end Itasca.Runtime.SourceMachine.Float

end

/-! ## Transition -/

section

namespace Itasca.Runtime.SourceMachine.Float
open SpecExt Itasca.Runtime.Spec

/-- Relational scalar float transition: every permitted NaN result remains available. -/
inductive Transition (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction) : AResult → Prop where
  | next (front : List val) (a b bits : Nat)
      (values : f.vals = front ++ op.operands a b)
      (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
      (effect : op.Result a b (some bits)) :
      Transition s f rest after op
        (advance s { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } rest)
  | trap (front : List val) (a b : Nat)
      (values : f.vals = front ++ op.operands a b)
      (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
      (effect : op.Result a b none) : Transition s f rest after op .trap

theorem transition_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    ATyped next := by
  cases step with
  | next front a b bits values first second effect =>
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    apply active_frame_preservation typed (op.frame_preservation front a b bits typed.store effect.1 ?_) rfl
    change f.vals = front ++ op.operands a b at values
    simpa only [values] using hf

theorem Instruction.operands_length (op : Instruction) (a b : Nat) :
    (op.operands a b).length = op.arity := by cases op <;> rfl

theorem Instruction.prefix_bounds (op : Instruction) {s : store} {f : AFrame} {after : List instr}
    (typed : FrameTyped s { f with code := op.source :: after } [])
    (front : List val) (a b : Nat) (values : f.vals = front ++ op.operands a b) :
    Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨other, x, y, otherValues, _, _, _, heights⟩ := op.typed_operands typed
  have lengthEq : other.length = front.length := by
    have left := congrArg List.length values
    have right := congrArg List.length otherValues
    simp only [List.length_append, Instruction.operands_length] at left right
    omega
  constructor
  · intro value member
    have valid := (frame_typed_wf typed).2.2.1
    apply valid value
    change value ∈ f.vals
    rw [values]
    exact List.mem_append_left _ member
  · simpa only [lengthEq] using heights

theorem transition_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    NextSim ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ next := by
  cases step with
  | next front a b bits values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact frames_typed_wf h
    obtain ⟨hw, hl, _, hc⟩ := frame_typed_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    apply NextSim.single
    simpa only [values] using op.simulation s ambient f rest after front a b bits first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

theorem transition_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op .trap) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  cases step with
  | trap front a b values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact frames_typed_wf h
    obtain ⟨hw, hl, _, hc⟩ := frame_typed_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    simpa only [values] using op.trap_simulation s ambient f rest after front a b first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

end Itasca.Runtime.SourceMachine.Float

end

/-! ## Positive -/

section

namespace Itasca.Runtime.SourceMachine.Float
open SpecExt Itasca.Runtime.Spec
theorem transition_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    StepH (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) [] (decode next) := by
  cases step with
  | next front a b bits values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact frames_typed_wf h
    obtain ⟨hw, hl, _, hc⟩ := frame_typed_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    simpa only [values] using op.simulation s ambient f rest after front a b bits first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

end Itasca.Runtime.SourceMachine.Float

end
