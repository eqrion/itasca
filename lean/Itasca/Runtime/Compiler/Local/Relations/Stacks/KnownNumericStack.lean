import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack

/-!
Sections, each formerly its own module: KnownPopStack, KnownNumericStack.
-/

/-! ## KnownPopStack -/

section

/-!
A physical pop never inserts an unknown operand, including an implicit polymorphic pop. The returned operand may itself be unknown.

Main declarations: `concrete_popped_remainder` and `pop_with_type_concrete`. A direct consumer is `Compiler.Local.Relations.Stacks.KnownNumericStack`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca

/-- A physical pop never inserts an unknown operand, including an implicit
polymorphic pop. The returned operand may itself be unknown. -/
theorem concrete_popped_remainder {poly before value after}
    (known : ConcreteStack before) (popped : StackSemantics.Popped poly before value after) :
    ConcreteStack after := by
  cases popped with
  | explicit => exact (concrete_stack_append.mp known).1
  | implicit => simp [ConcreteStack]

theorem concrete_typed_pop_result {poly before expected result after}
    (known : ConcreteStack before) (effect : StackSemantics.TypedPopResult poly before expected result after) :
    ConcreteStack after := by
  cases result with
  | Ok value => exact concrete_popped_remainder known effect.1
  | Err error =>
    rcases effect with ⟨_, _, _, rfl⟩ | ⟨_, value, popped, _⟩
    · simp [ConcreteStack]
    · exact concrete_popped_remainder known popped

@[step] theorem pop_with_type_concrete (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : wasm_types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack segment) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ ConcreteStack rest ⦄ := by
  apply WP.spec_mono (code.pop_with_type.segment st outer segment expected values base)
  rintro ⟨result, after⟩ ⟨controls, position, rest, afterValues, effect⟩
  exact ⟨controls, position, rest, afterValues, concrete_typed_pop_result known effect⟩

end Itasca.Runtime.Compiler

end

/-! ## KnownNumericStack -/

section

/-!
Known operand-stack shape after a typed numeric pop.

Main declarations: `pop_with_type_known`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

theorem pop_with_type_known (st after : code.OpIterState) (outer segment : List code.StackType)
    (expected : wasm_types.ValueType) (result : core.result.Result code.StackType error.OpError)
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

end
