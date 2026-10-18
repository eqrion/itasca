import Exec.Code.Body.Reader.Control.ReaderBranchInfoWasm1
import Exec.Code.Body.Reader.Control.ReaderBranchEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- An accepted Wasm 1 branch has its exact target argument suffix in a live
concrete operand segment. -/
theorem reader_br_arguments_wasm1 (st out : code.OpIterState) (data : Slice U8)
    (depth : U32) (bt : code.BlockType) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_br st data = .ok (.Ok (depth, bt), out)) :
    ∃ front, Sequence.stackTypes segment = front ++ Control.resultTypes bt := by
  obtain ⟨middle, target, read, resultType⟩ := reader_branch_label_wasm1 st out data false depth bt accepted
  have readEffect := code.read_label.spec st data
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  obtain ⟨types, targetRead, targetTypes⟩ := WP.spec_imp_exists (code.branch_target_types.spec target)
  obtain ⟨⟨result, popped⟩, pop, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_types.realizes middle outer segment (alloc.vec.Vec.deref types)
      (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base))
  dsimp only at transfer
  cases result with
  | Err error => simp [code.read_br, read, targetRead, pop, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok unit =>
    have poly : Control.polymorphic middle = false := by simpa [Control.polymorphic, controls] using monomorphic
    rw [poly] at transfer
    refine ⟨Sequence.stackTypes rest, ?_⟩
    have exactTypes := (realized_concrete_types known (transfer _ (Sequence.realizes_default false rest))).symm
    simpa [alloc.vec.Vec.deref, targetTypes, resultType, Control.targetTypes, Control.resultTypes] using exactTypes

/-- An accepted conditional branch consumes only its condition and retains the
checked target arguments on its fallthrough path. -/
theorem reader_br_if_arguments_wasm1 (st out : code.OpIterState) (data : Slice U8)
    (depth : U32) (bt : code.BlockType) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (monomorphic : Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_br_if st data = .ok (.Ok (depth, bt), out)) :
    ∃ rest : List code.StackType, segment = rest ++ [.Val .I32] ∧
      out.vals.val = outer ++ rest ∧
      ∃ front, Sequence.stackTypes rest = front ++ Control.resultTypes bt := by
  obtain ⟨middle, target, read, resultType⟩ := reader_branch_label_wasm1 st out data true depth bt accepted
  have readEffect := code.read_label.spec st data
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  obtain ⟨types, targetRead, targetTypes⟩ := WP.spec_imp_exists (code.branch_target_types.spec target)
  have middleBase : (Control.base middle).val = outer.length := by simpa [Control.base, controls] using base
  have poly : Control.polymorphic middle = false := by simpa [Control.polymorphic, controls] using monomorphic
  obtain ⟨⟨conditionResult, conditionState⟩, popCondition, conditionControls, _, remaining, conditionValues, conditionEffect⟩ := WP.spec_imp_exists
    (code.pop_with_type.segment middle outer segment .I32 (by simpa [sameValues] using values) middleBase)
  dsimp only at conditionControls conditionValues conditionEffect
  cases conditionResult with
  | Err error => simp [code.read_br_if, read, targetRead, popCondition, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok raw =>
    rw [poly] at conditionEffect
    have segmentEq := typed_pop_exact known conditionEffect
    have remainingKnown : ConcreteStack remaining := (concreteStack_append.mp (segmentEq ▸ known)).1
    obtain ⟨⟨argumentResult, argumentState⟩, popArguments, argumentControls, _, rest, argumentValues, _, transfer⟩ := WP.spec_imp_exists
      (code.pop_types.realizes conditionState outer remaining (alloc.vec.Vec.deref types) conditionValues
        (by simpa [Control.base, conditionControls] using middleBase))
    dsimp only at argumentControls argumentValues transfer
    cases argumentResult with
    | Err error => simp [code.read_br_if, read, targetRead, popCondition, popArguments, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      have argumentPoly : Control.polymorphic conditionState = false := by
        simpa [Control.polymorphic, conditionControls] using poly
      rw [argumentPoly] at transfer
      have interpreted := realized_concrete_types remainingKnown (transfer _ (Sequence.realizes_default false rest))
      have restKnown := concrete_stack_transfer remainingKnown transfer
      obtain ⟨remainingTypes, remainingEq⟩ := (concreteStack_iff remaining).mp remainingKnown
      obtain ⟨restTypes, restEq⟩ := (concreteStack_iff rest).mp restKnown
      have rawTypes : remainingTypes = restTypes ++ types.val := by
        apply List.map_injective_iff.mpr Translate.valueType_injective
        simpa [remainingEq, restEq, Sequence.stackTypes, List.map_append, List.map_map,
          Function.comp_def, alloc.vec.Vec.deref] using interpreted.symm
      have remainingShape : remaining = rest ++ types.val.map code.StackType.Val := by
        simp [remainingEq, rawTypes, restEq]
      have capacity : argumentState.vals.val.length + (alloc.vec.Vec.deref types).val.length ≤ Usize.max := by
        simp only [alloc.vec.Vec.deref, Slice.from_val]
        have bound : st.vals.val.length ≤ Usize.max := by scalar_tac
        simp only [alloc.vec.Vec.deref, argumentValues, values, segmentEq, remainingShape,
          List.length_append, List.length_map, List.length_singleton] at *
        omega
      obtain ⟨final, push, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_types.spec argumentState (alloc.vec.Vec.deref types) capacity)
      cases unit
      simp [code.read_br_if, read, targetRead, popCondition, popArguments, push,
        core.result.Result.Insts.CoreOpsTry.branch, code.branch_target_bt.eq] at accepted
      have same : out = final := accepted.2.symm
      subst out
      refine ⟨remaining, segmentEq, ?_, Sequence.stackTypes rest, ?_⟩
      · simpa [argumentValues, remainingShape, List.append_assoc, alloc.vec.Vec.deref] using finalValues
      · simpa [alloc.vec.Vec.deref, targetTypes, resultType, Control.targetTypes, Control.resultTypes] using interpreted.symm
end Exec.Code
