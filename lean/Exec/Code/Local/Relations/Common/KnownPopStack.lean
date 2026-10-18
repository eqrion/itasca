import Exec.Code.Local.Relations.Control.KnownControlStack
namespace Exec.Code
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

/-- Popping any type vector preserves concrete operands on both acceptance and
rejection, without assuming monomorphic control. -/
@[step] theorem pop_types_concrete (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : Slice types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack segment) :
    code.pop_types st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ ConcreteStack rest ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ rest, p.1.vals.val = outer ++ rest ∧ ConcreteStack rest)
  · rintro ⟨current, index⟩ ⟨bound, controls, position, segment, currentValues, currentKnown⟩
    dsimp only at bound controls position currentValues currentKnown
    unfold code.pop_types_loop.body
    dsimp only
    split
    · simp only [WP.spec_ok]
      exact ⟨controls, position, segment, currentValues, currentKnown⟩
    · step as ⟨next, decrement⟩
      have inBounds : next.val < expected.val.length := by scalar_tac
      step as ⟨ty, tyEq⟩
      have currentBase : (Control.base current).val = outer.length := by
        simpa only [Control.base, controls] using base
      step with pop_with_type_concrete current outer segment ty currentValues currentBase currentKnown
        as ⟨result, after, afterControls, afterPosition, rest, afterValues, afterKnown⟩
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, Std.bind_assoc, bind_ok, bind_tc_ok, WP.spec_ok]
        exact ⟨afterControls.trans controls, afterPosition.trans position, rest, afterValues, afterKnown⟩
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        exact ⟨by scalar_tac, afterControls.trans controls, afterPosition.trans position,
          ⟨rest, afterValues, afterKnown⟩, by scalar_tac⟩
  · exact ⟨by simp, rfl, rfl, segment, values, known⟩

@[step] theorem pop_results_concrete (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (known : ConcreteStack segment) :
    code.pop_results st env view ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ ConcreteStack rest ⦄ := by
  cases view with
  | Empty =>
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, values, known⟩
  | One ty =>
    unfold code.pop_results
    step with pop_with_type_concrete st outer segment ty values base known
      as ⟨result, after, controls, position, rest, afterValues, afterKnown⟩
    cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | «Type» index part =>
    unfold code.pop_results
    step as ⟨i, castEq⟩
    split
    · simp only [WP.spec_ok]
      exact ⟨trivial, trivial, segment, values, known⟩
    · cases part <;> step as ⟨ty, tyEq⟩
      all_goals exact pop_types_concrete st outer segment _ values base known

end Exec.Code
