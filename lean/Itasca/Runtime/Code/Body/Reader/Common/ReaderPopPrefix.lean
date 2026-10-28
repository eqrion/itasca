import Itasca.Runtime.Code.Local.Relations.Common.KnownPopStack
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem popped_prefix {poly before value after}
    (popped : StackSemantics.Popped poly before value after) : after <+: before := by
  cases popped with
  | explicit => exact ⟨_, rfl⟩
  | implicit => exact ⟨[], by simp⟩

theorem typed_pop_prefix {poly before expected result after}
    (effect : StackSemantics.TypedPopResult poly before expected result after) : after <+: before := by
  cases result with
  | Ok value => exact popped_prefix effect.1
  | Err error =>
    rcases effect with ⟨_, _, _, rfl⟩ | ⟨_, value, popped, _⟩
    · exact List.nil_prefix
    · exact popped_prefix popped

@[step] theorem pop_with_type_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  apply WP.spec_mono (code.pop_with_type.segment st outer segment expected values base)
  rintro ⟨result, after⟩ ⟨controls, position, rest, afterValues, effect⟩
  exact ⟨controls, position, rest, afterValues, typed_pop_prefix effect⟩

@[step] theorem pop_types_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : Slice types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) :
    code.pop_types st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ rest, p.1.vals.val = outer ++ rest ∧ rest <+: segment)
  · rintro ⟨current, index⟩ ⟨bound, controls, position, currentSegment, currentValues, currentPrefix⟩
    dsimp only at bound controls position currentValues currentPrefix
    unfold code.pop_types_loop.body
    dsimp only
    split
    · simp only [WP.spec_ok]
      exact ⟨controls, position, currentSegment, currentValues, currentPrefix⟩
    · step as ⟨next, decrement⟩
      have inBounds : next.val < expected.val.length := by scalar_tac
      step as ⟨ty, tyEq⟩
      have currentBase : (Control.base current).val = outer.length := by
        simpa only [Control.base, controls] using base
      step with pop_with_type_prefix current outer currentSegment ty currentValues currentBase
        as ⟨result, after, afterControls, afterPosition, rest, afterValues, afterPrefix⟩
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
        exact ⟨afterControls.trans controls, afterPosition.trans position, rest, afterValues,
          afterPrefix.trans currentPrefix⟩
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        exact ⟨by scalar_tac, afterControls.trans controls, afterPosition.trans position,
          ⟨rest, afterValues, afterPrefix.trans currentPrefix⟩, by scalar_tac⟩
  · exact ⟨by simp, rfl, rfl, segment, values, ⟨[], by simp⟩⟩

@[step] theorem pop_results_prefix (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length) :
    code.pop_results st env view ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  cases view with
  | Empty =>
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, values, ⟨[], by simp⟩⟩
  | One ty =>
    unfold code.pop_results
    step with pop_with_type_prefix st outer segment ty values base
      as ⟨result, after, controls, position, rest, afterValues, afterPrefix⟩
    cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | «Type» index part =>
    unfold code.pop_results
    step as ⟨i, castEq⟩
    split
    · simp only [WP.spec_ok]
      exact ⟨trivial, trivial, segment, values, ⟨[], by simp⟩⟩
    · cases part <;> step as ⟨ty, tyEq⟩
      all_goals exact pop_types_prefix st outer segment _ values base
end Itasca.Runtime.Code
