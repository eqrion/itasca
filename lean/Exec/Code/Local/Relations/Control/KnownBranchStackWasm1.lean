import Exec.Code.Local.Relations.Control.KnownBranchStack
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

@[step] theorem pop_with_type_concrete_bounded (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack segment) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧ ConcreteStack rest ⦄ := by
  obtain ⟨⟨result, out⟩, run, controls, position, rest, afterValues, afterKnown⟩ := WP.spec_imp_exists
    (pop_with_type_concrete st outer segment expected values base known)
  have effect := code.pop_with_type.realizes st outer segment expected values base
  rw [run, WP.spec_ok] at effect
  obtain ⟨_, _, other, otherValues, bound, _⟩ := effect
  have same : rest = other := List.append_cancel_left (afterValues.symm.trans otherValues)
  rw [run, WP.spec_ok]
  exact ⟨controls, position, rest, afterValues, by simpa only [same] using bound, afterKnown⟩

@[step] theorem pop_types_concrete_bounded (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : Slice types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (known : ConcreteStack segment) :
    code.pop_types st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧ ConcreteStack rest ⦄ := by
  obtain ⟨⟨result, out⟩, run, controls, position, rest, afterValues, afterKnown⟩ := WP.spec_imp_exists
    (pop_types_concrete st outer segment expected values base known)
  have effect := code.pop_types.realizes st outer segment expected values base
  rw [run, WP.spec_ok] at effect
  obtain ⟨_, _, other, otherValues, bound, _⟩ := effect
  have same : rest = other := List.append_cancel_left (afterValues.symm.trans otherValues)
  rw [run, WP.spec_ok]
  exact ⟨controls, position, rest, afterValues, by simpa only [same] using bound, afterKnown⟩

/-- Scalar-profile conditional branches preserve concrete operands while
checking and restoring the target signature. -/
theorem wasm1_branch_if_concrete (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (capacity : st.vals.val.length + 1 ≤ Usize.max)
    (known : ConcreteStack st.vals.val) :
    code.read_br_if st data ⦃ out => ∀ depth bt, out.1 = .Ok (depth, bt) → ConcreteStack out.2.vals.val ⦄ := by
  have knownParts : ConcreteStack outer ∧ ConcreteStack segment := concreteStack_append.mp (values ▸ known)
  unfold code.read_br_if
  step with code.read_label.spec st data as ⟨result, decoded, sameValues, sameControls, _⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, target⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with code.branch_target_types.spec target as ⟨types, typesEq⟩
    step with pop_with_type_concrete_bounded decoded outer segment .I32
      (by simpa only [sameValues] using values) (by simpa only [Control.base, sameControls] using base) knownParts.2
      as ⟨condition, afterCondition, conditionControls, _, rest, conditionValues, conditionLength, conditionKnown⟩
    cases condition with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with pop_types_concrete_bounded afterCondition outer rest types.deref conditionValues
        (by simpa only [Control.base, conditionControls, sameControls] using base) conditionKnown
        as ⟨args, afterArgs, argsControls, _, tail, argsValues, argsLength, argsKnown⟩
      cases args with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok acceptedUnit =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have typeLength : types.val.length ≤ 1 := by rw [typesEq]; exact Control.targetTypes_length target
        have fits : afterArgs.vals.val.length + types.deref.val.length ≤ Usize.max := by
          simp only [values, List.length_append] at capacity
          simp only [argsValues, alloc.vec.Vec.deref, Slice.from_val, List.length_append]
          omega
        step with code.push_types.spec afterArgs types.deref fits as ⟨finalState, finalValues, _, _⟩
        step with code.branch_target_bt.spec target as ⟨bt, btEq⟩
        intro _ _ _
        rw [finalValues, argsValues]
        exact concreteStack_append.mpr ⟨concreteStack_append.mpr ⟨knownParts.1, argsKnown⟩, concrete_values _⟩
end Exec.Code
