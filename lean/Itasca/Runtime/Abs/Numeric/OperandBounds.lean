import Itasca.Runtime.Abs.Numeric.Operands
import Itasca.Runtime.Abs.Sim.Typed
namespace Itasca.Runtime.Abs.Numeric
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

end Itasca.Runtime.Abs.Numeric
