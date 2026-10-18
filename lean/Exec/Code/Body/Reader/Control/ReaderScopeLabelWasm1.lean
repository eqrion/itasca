import Exec.Code.Body.Reader.Control.ReaderScopeZipper
import Exec.Code.Body.Reader.Control.ReaderBranchInfoWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

private theorem spine_header {root parents C outer form}
    (spine : Wasm1.Frames.Spine root parents C outer form) (saved : Wasm1.Frames.Saved)
    (member : saved ∈ parents) : ∃ context, Wasm1.Frames.Header context saved := by
  induction spine with
  | root => simp at member
  | push parents context outer parent child spine header base resume notBody ih =>
    rcases List.mem_append.mp member with member | member
    · exact ih member
    · simp only [List.mem_singleton] at member
      subst saved
      exact ⟨context, header⟩

theorem ReaderScopeZipperWasm1.label {parents current savedParents savedCurrent root st}
    (same : ReaderScopeZipperWasm1 parents current savedParents savedCurrent)
    (opened : Wasm1.Frames.Open root st savedParents savedCurrent)
    (depth : Nat) (target : code.Ctrl)
    (selected : st.ctrls.val.reverse[depth]? = some target) :
    ∃ scope, (current :: parents.reverse)[depth]? = some scope ∧
      scope.branchTypes = (Control.targetTypes target).map Translate.valueType := by
  obtain ⟨C, outer, spine, header, base, typed, controls, values⟩ := id opened
  have mapped : st.ctrls.val.reverse = (savedCurrent :: savedParents.reverse).map Wasm1.Frames.Saved.ctrl := by
    simp [controls, List.reverse_append, List.map_reverse]
  rw [mapped, List.getElem?_map] at selected
  cases found : (savedCurrent :: savedParents.reverse)[depth]? with
  | none => simp [found] at selected
  | some saved =>
    simp only [found, Option.map_some, Option.some.injEq] at selected
    subst target
    obtain ⟨scope, scopeFound, matchScope⟩ := same.lookup depth saved found
    have member : saved ∈ savedCurrent :: savedParents.reverse := by
      obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
      exact same ▸ List.getElem_mem bound
    have savedHeader : ∃ context, Wasm1.Frames.Header context saved := by
      rcases List.mem_cons.mp member with equal | outerMember
      · subst saved; exact ⟨C, header⟩
      · exact spine_header spine saved (by simpa using outerMember)
    obtain ⟨context, savedHeader⟩ := savedHeader
    exact ⟨scope, scopeFound, matchScope.branchTypes.trans savedHeader.label⟩

/-- The actual reader selects a compiler source scope with exactly its reported target types. -/
theorem reader_branch_scope_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {parents current}
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (conditional : Bool) (depth : U32) (resultBt : code.BlockType) (out : code.OpIterState)
    (accepted : (if conditional then code.read_br_if st data else code.read_br st data) =
      .ok (.Ok (depth, resultBt), out)) :
    ∃ target, (current :: parents.reverse)[depth.val]? = some target ∧
      target.branchTypes = Control.resultTypes resultBt := by
  obtain ⟨middle, selected, read, resultType⟩ := reader_branch_label_wasm1 st out data conditional depth resultBt accepted
  have effect := code.read_label.spec st data
  rw [read, WP.spec_ok] at effect
  obtain ⟨_, _, decoded, bound, lookup⟩ := effect
  try dsimp only at bound lookup
  have reversed : st.ctrls.val.reverse[depth.val]? = some selected := by
    simp only [List.getElem?_reverse bound, List.getElem?_eq_getElem (by omega : st.ctrls.val.length - 1 - depth.val < st.ctrls.val.length)]
    exact congrArg some lookup.symm
  obtain ⟨scope, found, types⟩ := same.label p.opened depth.val selected reversed
  exact ⟨scope, found, by simpa [Control.resultTypes, Control.targetTypes, resultType] using types⟩
end Exec.Code
