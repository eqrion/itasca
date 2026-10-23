import Exec.Code.Local.Callbacks.Control.ScopeFrameSelect
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderBranchEffects
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_br_layout_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (view : signature.ResultType) (out : code.BodyState)
    (accepted : code.branch_info st data env false = .ok (.Ok (depth, view), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes st.core.vals.val = scope.front ++ discarded ++ scope.branchTypes := by
  have selected := reader_branch_info_selected st data env false depth view out p.opened.shape.aligned accepted
  obtain ⟨scope, types, scopeAt, resolved, branchTypes⟩ := same.label p.opened depth.val view selected
  obtain ⟨_, outer, spine, _, base, _, controls, _, values⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (values ▸ known)).2
  obtain ⟨front, arguments⟩ := reader_br_arguments st out data env depth view types outer p.current.vals
    values (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown resolved p.opened.shape.aligned accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt p.current.vals front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_⟩
  simpa only [values, wasm2_spine_values spine, List.flatMap_def] using whole

end Exec.Code
