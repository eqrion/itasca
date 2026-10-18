import Exec.Code.Body.Reader.Control.ReaderScopeZipper
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Control.ReaderBranchEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- One actual BR reader identifies both its literal source instruction and matched target scope. -/
theorem reader_br_scoped_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {parents current}
    (scopes : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (live : p.current.ctrl.polymorphic_base = false) (known : ConcreteStack p.current.vals)
    {V : Type} (visitor : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0c#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth view target front,
      visitor.on_br before out.core depth view = .ok (.Ok (), after) ∧
      ReaderPostWasm2 p out.core (.BR (.mk_uN depth.val)) true [] ∧
      (current :: parents.reverse)[depth.val]? = some target ∧
      Sequence.stackTypes p.current.vals = front ++ target.branchTypes := by
  obtain ⟨depth, view, callback, read, post⟩ := reader_br_wasm2 p visitor before after out ctx byte accepted
  have selected := reader_branch_info_selected st data env false depth view out p.opened.shape.aligned read
  obtain ⟨target, types, found, resolved, typesEq⟩ := scopes.label p.opened depth.val view selected
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, values⟩ := id p.opened
  obtain ⟨front, arguments⟩ := reader_br_arguments st out data env depth view types outer p.current.vals values
    (by simp [Control.base, controls, base]) (by simp [Control.polymorphic, controls, live]) known
    resolved p.opened.shape.aligned read
  exact ⟨depth, view, target, front, callback, post, found, by simpa [typesEq] using arguments⟩

/-- One actual BR_IF reader removes exactly the i32 condition and selects the matched target. -/
theorem reader_br_if_scoped_wasm2 {data env locals index st}
    (p : Pending data env locals index st) {parents current}
    (scopes : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (live : p.current.ctrl.polymorphic_base = false) (known : ConcreteStack p.current.vals)
    {V : Type} (visitor : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0x0d#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth view target values rest front,
      visitor.on_br_if before out.core depth view = .ok (.Ok (), after) ∧
      ReaderPostWasm2 p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ∧
      (current :: parents.reverse)[depth.val]? = some target ∧
      p.current.vals = rest ++ [.Val .I32] ∧ values = rest ∧
      Sequence.stackTypes rest = front ++ target.branchTypes := by
  obtain ⟨depth, view, values, callback, read, post⟩ := reader_br_if_wasm2 p visitor before after out ctx byte accepted
  have selected := reader_branch_info_selected st data env true depth view out p.opened.shape.aligned read
  obtain ⟨target, types, found, resolved, typesEq⟩ := scopes.label p.opened depth.val view selected
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, oldValues⟩ := id p.opened
  obtain ⟨rest, split, newValues, front, arguments⟩ := reader_br_if_arguments st out data env depth view types outer p.current.vals oldValues
    (by simp [Control.base, controls, base]) (by simp [Control.polymorphic, controls, live]) known
    resolved p.opened.shape.aligned read
  have outerEq := wasm2_spine_values spine
  have afterValues := post.values.2
  have same : values = rest := by
    rw [afterValues] at newValues
    simpa only [outerEq, List.append_cancel_left_eq] using newValues
  exact ⟨depth, view, target, values, rest, front, callback, post, found, split, same,
    by simpa [typesEq] using arguments⟩
end Exec.Code
