import Itasca.Runtime.SourceMachine.StepSafety
import Itasca.Runtime.SourceMachine.Sim.Call
import Itasca.Runtime.SourceMachine.Sim.Trap
import Itasca.Runtime.SourceMachine.Sim.Local

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- A successful abstract step either performs positive source work or is an
exact decoding stutter that strictly decreases the administrative potential. -/
def NextSim (s next : AState) : Prop :=
  (decode s = decode next ∧ administrativeMeasure next < administrativeMeasure s) ∨
  ∃ n, 0 < n ∧ StepsHN n (decode s) [] (decode next)

theorem NextSim.single {s next : AState} (h : StepH (decode s) [] (decode next)) : NextSim s next :=
  Or.inr ⟨1, by omega, by simpa only [List.nil_append] using StepsHN.cons h (StepsHN.refl (step_h_wf h).2)⟩

theorem NextSim.counted {s next : AState} {n : Nat}
    (h : StepsHN n (decode s) [] (decode next)) (hn : 0 < n) : NextSim s next :=
  Or.inr ⟨n, hn, h⟩

/-- Operand inversion also proves that no consumed value belongs to a saved
outer label prefix. -/
theorem frame_typed_operands_bounds {s : store} {f : AFrame} {op : instr} {code : List instr}
    (h : FrameTyped s { f with code := op :: code } []) :
    ∃ C first operands ins outs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      f.vals = first ++ operands ∧ ResultsTyped s ins operands ∧
      Forall wf_val first ∧ (∀ label ∈ f.labels, label.height ≤ first.length) := by
  cases h with
  | mk C bindings locals hlocals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, heq, heights⟩ := code_stack_head_bounds (value_types_concrete f.vals) hc
    have values' : ResultsTyped s (front ++ ins) f.vals := by rw [← heq]; exact values
    obtain ⟨first, operands, hsplit, hfirst, hoperands⟩ := results_typed_split values'
    refine ⟨C, first, operands, ins, outs, bindings, locals, hop, hsplit, hoperands,
      results_typed_wf hfirst, ?_⟩
    intro label hm
    rw [results_typed_length hfirst]
    exact heights label hm

end Itasca.Runtime.SourceMachine
