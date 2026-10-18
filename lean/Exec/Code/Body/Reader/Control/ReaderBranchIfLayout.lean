import Exec.Code.Body.Reader.Control.ReaderBranchLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_br_if_layout_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (view : signature.ResultType) (out : code.BodyState)
    (accepted : code.branch_info st data env true = .ok (.Ok (depth, view), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes st.core.vals.val = Sequence.stackTypes out.core.vals.val ++ [.I32] ∧
      Sequence.stackTypes out.core.vals.val = scope.front ++ discarded ++ scope.branchTypes ∧
      ConcreteStack out.core.vals.val := by
  have selected := reader_branch_info_selected st data env true depth view out p.opened.shape.aligned accepted
  obtain ⟨scope, types, scopeAt, resolved, branchTypes⟩ := same.label p.opened depth.val view selected
  obtain ⟨_, outer, spine, _, base, _, controls, _, values⟩ := p.opened
  have both := concreteStack_append.mp (values ▸ known)
  obtain ⟨rest, input, output, front, arguments⟩ := reader_br_if_arguments st out data env depth view types outer p.current.vals
    values (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) both.2 resolved p.opened.shape.aligned accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt rest front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_, ?_, ?_⟩
  · simp [values, input, output, Sequence.stackTypes, List.append_assoc, Translate.valueType]
  · simpa only [output, wasm2_spine_values spine, List.flatMap_def] using whole
  · rw [output]
    exact concreteStack_append.mpr ⟨both.1, (concreteStack_append.mp (input ▸ both.2)).1⟩

theorem reader_br_if_layout_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {parents current}
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (known : ConcreteStack st.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (resultBt : code.BlockType) (out : code.OpIterState)
    (accepted : code.read_br_if st data = .ok (.Ok (depth, resultBt), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes st.vals.val = Sequence.stackTypes out.vals.val ++ [.I32] ∧
      Sequence.stackTypes out.vals.val = scope.front ++ discarded ++ scope.branchTypes ∧
      ConcreteStack out.vals.val := by
  obtain ⟨scope, scopeAt, branchTypes⟩ := reader_branch_scope_wasm1 p same true depth resultBt out accepted
  obtain ⟨_, outer, spine, _, base, _, controls, values⟩ := p.opened
  have both := concreteStack_append.mp (values ▸ known)
  obtain ⟨rest, input, output, front, arguments⟩ := reader_br_if_arguments_wasm1 st out data depth resultBt outer p.current.vals
    values (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) both.2 accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt rest front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_, ?_, ?_⟩
  · simp [values, input, output, Sequence.stackTypes, List.append_assoc, Translate.valueType]
  · simpa only [output, wasm1_spine_values spine, List.flatMap_def] using whole
  · rw [output]
    exact concreteStack_append.mpr ⟨both.1, (concreteStack_append.mp (input ▸ both.2)).1⟩
end Exec.Code
