import Exec.Code.Local.Callbacks.Control.ScopeFrameSelect
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderScopeLabelWasm1
import Exec.Code.Body.Reader.Control.ReaderBranchEffectsWasm1
import Exec.Code.Body.Reader.Control.ReaderBranchEffects
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Exact live branch slot coordinates follow from source scope selection and
the compiler's current layout; no equality of word widths substitutes for a
target's source type list. -/
theorem CompilerPrefix.branch_layout {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = scope.front ++ discarded ++ scope.branchTypes) :
    ∃ index : Usize, ∃ frame : runtime.compiler.Frame, ∃ source : U32,
      before.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = before.frames.val.length ∧
      FrameScope locals before scope frame ∧
      frame.height.val = slots locals + slots scope.front ∧
      source.val = slots locals + slots (scope.front ++ discarded) ∧
      source.val + slots scope.branchTypes = before.height.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, found, position, shape, _, height⟩ :=
    invariant.frames.selected_live invariant.entryChain entered depth scope selected
  obtain ⟨source, sourcePosition, sourceWidth⟩ := branch_source_coordinate
    (input ▸ retained.layout) retained.localsEq
  exact ⟨index, frame, source, found, position, shape, height, sourcePosition, sourceWidth⟩

theorem reader_br_layout_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {parents current}
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

theorem reader_br_layout_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {parents current}
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (known : ConcreteStack st.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base = false)
    (depth : U32) (resultBt : code.BlockType) (out : code.OpIterState)
    (accepted : code.read_br st data = .ok (.Ok (depth, resultBt), out)) :
    ∃ scope discarded,
      (current :: parents.reverse)[depth.val]? = some scope ∧
      Sequence.stackTypes st.vals.val = scope.front ++ discarded ++ scope.branchTypes := by
  obtain ⟨scope, scopeAt, branchTypes⟩ := reader_branch_scope_wasm1 p same false depth resultBt out accepted
  obtain ⟨_, outer, spine, _, base, _, controls, values⟩ := p.opened
  have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (values ▸ known)).2
  obtain ⟨front, arguments⟩ := reader_br_arguments_wasm1 st out data depth resultBt outer p.current.vals
    values (by simpa [Control.base, controls] using base)
    (by simpa [Control.polymorphic, controls] using monomorphic) segmentKnown accepted
  obtain ⟨discarded, whole⟩ := fronts.branch depth.val scope scopeAt p.current.vals front (by simpa only [branchTypes] using arguments)
  refine ⟨scope, discarded, scopeAt, ?_⟩
  simpa only [values, wasm1_spine_values spine, List.flatMap_def] using whole
end Exec.Code
