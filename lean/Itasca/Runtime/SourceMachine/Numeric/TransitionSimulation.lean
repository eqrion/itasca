import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Sim.Structured
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety

/-!
Sections, each formerly its own module: OperandBounds, TransitionSimulation.
-/

/-! ## OperandBounds -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec
 theorem Instruction.typed_operands_bounds (op : Instruction) {s : store} {f : AFrame}
    {after : List instr} (typed : FrameTyped s { f with code := op.source :: after } []) :
    ∃ front a b, f.vals = front ++ op.operands a b ∧ Forall wf_val front ∧
      (∀label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands, hfirst, heights⟩ := frame_typed_operands_bounds typed
  cases op <;> cases hop
  all_goals
    first
    | cases hoperands with
      | cons hl hr =>
        cases hr with
        | cons hr hend =>
          cases hend
          obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
          obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
          obtain ⟨wa, hwa⟩ := word_exists _ a ha
          obtain ⟨wb, hwb⟩ := word_exists _ b hb
          exact ⟨first, wa, wb, by simpa [Instruction.operands, Instruction.arity, Instruction.input, hwa, hwb] using hsplit, hfirst, heights⟩
    | cases hoperands with
      | cons hv hend =>
        cases hend
        obtain ⟨a, rfl, ha⟩ := integer_val_inv hv
        obtain ⟨wa, hwa⟩ := word_exists _ a ha
        exact ⟨first, wa, wa, by simpa [Instruction.operands, Instruction.arity, Instruction.input, hwa] using hsplit, hfirst, heights⟩

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## TransitionSimulation -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem transition_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op = .next next) :
    NextSim ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ next := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact frames_typed_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frame_typed_wf hf
  obtain ⟨front, a, b, values, hfront, heights⟩ := op.typed_operands_bounds hf
  have same : { f with code := op.source :: after } =
      { f with code := op.source :: after, vals := front ++ op.operands a b } := by
    cases f; simp_all
  conv at step => lhs; arg 2; rw [same]
  rw [transition_operands _ { f with code := op.source :: after } rest after front op a b, finish] at step
  cases resultEq : op.apply a b with
  | none => simp only [resultEq, reduceCtorEq] at step
  | some result =>
    simp only [resultEq, advance, AResult.next.injEq] at step
    rw [← step]
    apply NextSim.single
    simpa only [values] using op.simulation s ambient f rest after front a b result resultEq
      typed.store typed.ambient hw hl hfront (fun i hi => hc i (by simp [hi])) hr heights

theorem transition_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op = .trap) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact frames_typed_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frame_typed_wf hf
  obtain ⟨front, a, b, values, hfront, heights⟩ := op.typed_operands_bounds hf
  have same : { f with code := op.source :: after } =
      { f with code := op.source :: after, vals := front ++ op.operands a b } := by
    cases f; simp_all
  conv at step => lhs; arg 2; rw [same]
  rw [transition_operands _ { f with code := op.source :: after } rest after front op a b, finish] at step
  cases resultEq : op.apply a b with
  | none =>
    simpa only [values] using op.trap_simulation s ambient f rest after front a b resultEq
      typed.store typed.ambient hw hl hfront (fun i hi => hc i (by simp [hi])) hr heights
  | some result => simp only [resultEq, advance, reduceCtorEq] at step
theorem astep_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ next := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op hf] at step
  exact transition_simulation s ambient f rest after op next typed step

theorem astep_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .trap) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op hf] at step
  exact transition_trap_simulation s ambient f rest after op typed step

end Itasca.Runtime.SourceMachine.Numeric

end
