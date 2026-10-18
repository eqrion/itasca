import Exec.Code.Local.Relations.Common.KnownPopStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

theorem pop_with_type_known (st after : code.OpIterState) (outer segment : List code.StackType)
    (expected : types.ValueType) (result : core.result.Result code.StackType error.OpError)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (known : ConcreteStack st.vals.val)
    (accepted : code.pop_with_type st expected = .ok (result, after)) :
    ∃ rest, after.ctrls = st.ctrls ∧ after.pos = st.pos ∧ after.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ ConcreteStack after.vals.val := by
  have segmentKnown := (concreteStack_append.mp (values ▸ known)).2
  have effect := code.pop_with_type.realizes st outer segment expected values base
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨controls, position, rest, afterValues, length, _⟩ := effect
  have knowledge := pop_with_type_concrete st outer segment expected values base segmentKnown
  rw [accepted, WP.spec_ok] at knowledge
  obtain ⟨_, _, rest', afterValues', restKnown⟩ := knowledge
  exact ⟨rest, controls, position, afterValues, length, afterValues'.symm ▸
    concreteStack_append.mpr ⟨(concreteStack_append.mp (values ▸ known)).1, restKnown⟩⟩

theorem read_conversion_known (st out : code.OpIterState) (outer segment : List code.StackType)
    (input output : types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (size : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val)
    (accepted : code.read_conversion st input output = .ok (.Ok (), out)) :
    ConcreteStack out.vals.val := by
  unfold code.read_conversion at accepted
  obtain ⟨⟨result, middle⟩, popped, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    obtain ⟨tail, controls, position, vals, shrink, nextKnown⟩ :=
      pop_with_type_known st middle outer segment input (.Ok value) values base known popped
    have fits : middle.vals.val.length < Usize.max := by
      simp only [vals, values, List.length_append] at *
      omega
    obtain ⟨after, pushed, afterValues, _, _⟩ := WP.spec_imp_exists (code.push_val.spec middle (.Val output) fits)
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, pushed,
      Result.ok.injEq, Prod.mk.injEq, true_and] at rest
    subst out
    rw [afterValues]
    exact concreteStack_append.mpr ⟨nextKnown, by simp [ConcreteStack]⟩

theorem read_binary_known (st out : code.OpIterState) (outer segment : List code.StackType)
    (input output : types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (size : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val)
    (accepted : code.read_binary st input output = .ok (.Ok (), out)) :
    ConcreteStack out.vals.val := by
  unfold code.read_binary at accepted
  obtain ⟨⟨result, middle⟩, popped, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    obtain ⟨tail, controls, position, vals, shrink, nextKnown⟩ :=
      pop_with_type_known st middle outer segment input (.Ok value) values base known popped
    have fits : middle.vals.val.length < Usize.max := by
      simp only [vals, values, List.length_append] at *
      omega
    have base' : (Control.base middle).val = outer.length := by
      simpa only [Control.base, controls] using base
    have rest' : code.read_conversion middle input output = .ok (.Ok (), out) := by
      simpa only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        code.read_conversion] using rest
    exact read_conversion_known middle out outer tail input output vals base' fits nextKnown rest'

theorem numeric_read_known (op : Numeric.Operation) (st out : code.OpIterState)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (size : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val)
    (accepted : Numeric.read op st = .ok (.Ok (), out)) : ConcreteStack out.vals.val := by
  unfold Numeric.read at accepted
  split at accepted
  · exact read_binary_known st out outer segment op.input op.output values base size known accepted
  · exact read_conversion_known st out outer segment op.input op.output values base size known accepted
end Exec.Code
