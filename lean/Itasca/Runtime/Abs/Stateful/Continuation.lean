import Itasca.Runtime.Abs.Stateful.Signature
import Itasca.Runtime.Abs.Sim.Typed
import Itasca.Runtime.Abs.Core.Typing
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

/-- A typed active instruction exposes its actual operands and the continuation
for any result values of the instruction's generated output type. -/
theorem frame_operands {s : store} {f : AFrame} {op : instr} {code : List instr}
    (typed : FrameTyped s {f with code := op :: code} []) :
    ∃ C front operands inputs outputs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list inputs,.mk_list outputs⟩ ∧
      f.vals = front ++ operands ∧ ResultsTyped s inputs operands ∧
      Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      (∀ produced, ResultsTyped s outputs produced →
        FrameTyped s {f with code := code, vals := front ++ produced} []) := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨prefixTypes,inputs,outputs,operation,splitTypes,continuation,heights⟩ :=
      codeStack_after_bounds (value_types_concrete f.vals) hc
    have all : ResultsTyped s (prefixTypes ++ inputs) f.vals := by rw [←splitTypes]; exact values
    obtain ⟨front,operands,split,frontTyped,operandTyped⟩ := resultsTyped_split all
    refine ⟨C,front,operands,inputs,outputs,bindings,localTypes,operation,split,operandTyped,
      resultsTyped_wf frontTyped,?_,?_⟩
    · intro label member
      rw [resultsTyped_length frontTyped]
      exact heights label member
    · intro produced producedTyped
      have typedValues := List.rel_append frontTyped producedTyped
      have resultTypes := results_type_of_typed typedValues
      apply FrameTyped.mk (f := {f with code := code,vals := front ++ produced}) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped,resultTypes] using typedValues
      · simpa only [List.append_nil,resultTypes] using continuation

end Itasca.Runtime.Abs.Stateful
