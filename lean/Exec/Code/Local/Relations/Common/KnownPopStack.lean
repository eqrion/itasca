import Exec.Code.Local.Relations.Control.KnownControlStack
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca

/-- A physical pop never inserts an unknown operand, including an implicit
polymorphic pop. The returned operand may itself be unknown. -/
theorem concrete_popped_remainder {poly before value after}
    (known : ConcreteStack before) (popped : StackSemantics.Popped poly before value after) :
    ConcreteStack after := by
  cases popped with
  | explicit => exact (concreteStack_append.mp known).1
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
    (expected : types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack segment) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ ConcreteStack rest ⦄ := by
  apply WP.spec_mono (code.pop_with_type.segment st outer segment expected values base)
  rintro ⟨result, after⟩ ⟨controls, position, rest, afterValues, effect⟩
  exact ⟨controls, position, rest, afterValues, concrete_typed_pop_result known effect⟩

end Itasca.Runtime.Code
