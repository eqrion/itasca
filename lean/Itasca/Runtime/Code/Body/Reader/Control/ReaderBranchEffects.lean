import Itasca.Runtime.Code.Body.Reader.Control.ReaderBranchInfo
import Itasca.Runtime.Code.Body.Reader.Local.ReaderLocalEffects
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- Checked branch arguments form the exact source suffix of a live concrete stack. -/
theorem reader_br_arguments (st out : code.BodyState) (data : Slice U8) (env : module.Env)
    (depth : U32) (view : signature.ResultType) (expected : List types.ValueType)
    (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (monomorphic : Control.polymorphic st.core = false) (known : ConcreteStack segment)
    (resolved : resolve env view = some expected)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env false = .ok (.Ok (depth, view), out)) :
    ∃ front : List valtype, Sequence.stackTypes segment = front ++ expected.map Translate.valueType := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env false depth view out accepted
  have readEffect := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  obtain ⟨⟨result, popped⟩, pop, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_results.realizes middle.core env view expected outer segment resolved
      (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base))
  dsimp only at transfer
  cases result with
  | Err error => simp [code.branch_info, read, pop, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok unit =>
    cases unit
    have poly : Control.polymorphic middle.core = false := by simpa [Control.polymorphic, controls] using monomorphic
    rw [poly] at transfer
    exact ⟨Sequence.stackTypes rest, (realized_concrete_types known (transfer rfl _ (Sequence.realizes_default false rest))).symm⟩

/-- Conditional branches consume exactly the condition and retain the checked target arguments. -/
theorem reader_br_if_arguments (st out : code.BodyState) (data : Slice U8) (env : module.Env)
    (depth : U32) (view : signature.ResultType) (expected : List types.ValueType)
    (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (monomorphic : Control.polymorphic st.core = false) (known : ConcreteStack segment)
    (resolved : resolve env view = some expected)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env true = .ok (.Ok (depth, view), out)) :
    ∃ rest : List code.StackType, segment = rest ++ [.Val .I32] ∧
      out.core.vals.val = outer ++ rest ∧
      ∃ front : List valtype, Sequence.stackTypes rest = front ++ expected.map Translate.valueType := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env true depth view out accepted
  have readEffect := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  have middleBase : (Control.base middle.core).val = outer.length := by simpa [Control.base, controls] using base
  have poly : Control.polymorphic middle.core = false := by simpa [Control.polymorphic, controls] using monomorphic
  obtain ⟨⟨conditionResult, conditionState⟩, popCondition, conditionControls, _, remaining, conditionValues, conditionEffect⟩ := WP.spec_imp_exists
    (code.pop_with_type.segment middle.core outer segment .I32 (by simpa [sameValues] using values) middleBase)
  dsimp only at conditionControls conditionValues conditionEffect
  cases conditionResult with
  | Err error => simp [code.branch_info, read, popCondition, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok raw =>
    rw [poly] at conditionEffect
    have segmentEq := typed_pop_exact known conditionEffect
    have remainingKnown : ConcreteStack remaining := (concreteStack_append.mp (segmentEq ▸ known)).1
    obtain ⟨⟨argumentResult, argumentState⟩, popArguments, argumentControls, _, rest, argumentValues, _, transfer⟩ := WP.spec_imp_exists
      (code.pop_results.realizes conditionState env view expected outer remaining resolved conditionValues
        (by simpa [Control.base, conditionControls] using middleBase))
    dsimp only at argumentControls argumentValues transfer
    cases argumentResult with
    | Err error => simp [code.branch_info, read, popCondition, popArguments, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      have argumentPoly : Control.polymorphic conditionState = false := by
        simpa [Control.polymorphic, conditionControls] using poly
      rw [argumentPoly] at transfer
      have interpreted := realized_concrete_types remainingKnown (transfer rfl _ (Sequence.realizes_default false rest))
      have restKnown := concrete_stack_transfer remainingKnown (transfer rfl)
      obtain ⟨remainingTypes, remainingEq⟩ := (concreteStack_iff remaining).mp remainingKnown
      obtain ⟨restTypes, restEq⟩ := (concreteStack_iff rest).mp restKnown
      have rawTypes : remainingTypes = restTypes ++ expected := by
        apply List.map_injective_iff.mpr Translate.valueType_injective
        simpa [remainingEq, restEq, Sequence.stackTypes, List.map_append, List.map_map,
          Function.comp_def] using interpreted.symm
      have remainingShape : remaining = rest ++ expected.map code.StackType.Val := by
        simp [remainingEq, rawTypes, restEq]
      have capacity : argumentState.vals.val.length + expected.length ≤ Usize.max := by
        have bound : st.core.vals.val.length ≤ Usize.max := by scalar_tac
        simp only [argumentValues, values, segmentEq, remainingShape, List.length_append,
          List.length_map, List.length_singleton] at *
        omega
      obtain ⟨⟨pushResult, final⟩, push, pushOk, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_results.spec argumentState env view expected resolved capacity)
      cases pushResult with
      | Err error => contradiction
      | Ok unit =>
        simp [code.branch_info, read, popCondition, popArguments, push,
          core.result.Result.Insts.CoreOpsTry.branch] at accepted
        subst out
        refine ⟨remaining, segmentEq, ?_, Sequence.stackTypes rest, interpreted.symm⟩
        simpa [argumentValues, remainingShape, List.append_assoc] using finalValues
end Itasca.Runtime.Code
