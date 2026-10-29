import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack

/-!
Known operand-stack shape after a typed numeric pop.

Main declarations: `pop_with_type_known`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

theorem pop_with_type_known (st after : code.OpIterState) (outer segment : List code.StackType)
    (expected : types.ValueType) (result : core.result.Result code.StackType error.OpError)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (known : ConcreteStack st.vals.val)
    (accepted : code.pop_with_type st expected = .ok (result, after)) :
    ∃ rest, after.ctrls = st.ctrls ∧ after.pos = st.pos ∧ after.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ ConcreteStack after.vals.val := by
  have segmentKnown := (concrete_stack_append.mp (values ▸ known)).2
  have effect := code.pop_with_type.realizes st outer segment expected values base
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨controls, position, rest, afterValues, length, _⟩ := effect
  have knowledge := pop_with_type_concrete st outer segment expected values base segmentKnown
  rw [accepted, WP.spec_ok] at knowledge
  obtain ⟨_, _, rest', afterValues', restKnown⟩ := knowledge
  exact ⟨rest, controls, position, afterValues, length, afterValues'.symm ▸
    concrete_stack_append.mpr ⟨(concrete_stack_append.mp (values ▸ known)).1, restKnown⟩⟩

end Itasca.Runtime.Compiler
