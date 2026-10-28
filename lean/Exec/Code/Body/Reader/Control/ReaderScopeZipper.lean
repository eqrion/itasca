import Exec.Code.Body.Reader.Control.ReaderScopeWasm2
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem matched_at {α β : Type} {R : α → β → Prop} {left right}
    (same : List.Forall₂ R left right) (index : Nat) (value : β)
    (found : right[index]? = some value) : ∃ item, left[index]? = some item ∧ R item value := by
  induction same generalizing index with
  | nil => simp at found
  | @cons a b left right head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; exact ⟨a, rfl, head⟩
    | succ index => exact ih index (by simpa using found)

private theorem matched_last {α β : Type} {R : α → β → Prop} {left right value}
    (same : List.Forall₂ R left (right ++ [value])) :
    ∃ beginning item, left = beginning ++ [item] ∧ List.Forall₂ R beginning right ∧ R item value := by
  have beginning := List.forall₂_take_append left right [value] same
  have ending := List.forall₂_drop_append left right [value] same
  have singleton : ∀ {items : List α}, List.Forall₂ R items [value] → ∃ item, items = [item] ∧ R item value := by
    intro items related
    cases related with
    | cons head tail => cases tail; exact ⟨_, rfl, head⟩
  obtain ⟨item, rest, related⟩ := singleton ending
  exact ⟨left.take right.length, item, by rw [← rest, List.take_append_drop], beginning, related⟩

/-- Compiler source scopes and the canonical validator zipper retain the same source syntax. -/
structure ReaderScopeZipperWasm2 (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Wasm2.Frames.Saved) (savedCurrent : Wasm2.Frames.Saved) : Prop where
  parents : List.Forall₂ SourceScopeMatchesWasm2 parents savedParents
  current : SourceScopeMatchesWasm2 current savedCurrent

theorem ReaderScopeZipperWasm2.advance {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (token : Wasm2.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    ReaderScopeZipperWasm2 parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  ⟨same.parents, (SourceScopeMatchesWasm2.advance_iff _ _ _ _).mpr same.current⟩

theorem ReaderScopeZipperWasm2.enter {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (child : SourceScope) (savedChild : Wasm2.Frames.Saved)
    (fresh : SourceScopeMatchesWasm2 child savedChild) (remaining : List code.StackType) :
    ReaderScopeZipperWasm2 (parents ++ [current]) child
      (savedParents ++ [{savedCurrent with vals := remaining}]) savedChild :=
  ⟨List.rel_append same.parents (.cons (same.current.suspend remaining) .nil), fresh⟩

theorem ReaderScopeZipperWasm2.begin_else {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (type : blocktype) (condition : U32) (form : current.form = .then_ type condition)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderScopeZipperWasm2 parents (current.begin_else type condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  ⟨same.parents, same.current.begin_else type condition form yesExit noEntry normal⟩

theorem ReaderScopeZipperWasm2.lookup {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (depth : Nat) (saved : Wasm2.Frames.Saved)
    (found : (savedCurrent :: savedParents.reverse)[depth]? = some saved) :
    ∃ scope, (current :: parents.reverse)[depth]? = some scope ∧ SourceScopeMatchesWasm2 scope saved :=
  matched_at (.cons same.current (List.rel_reverse same.parents)) depth saved found

theorem ReaderScopeZipperWasm2.close {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (grandparents : List Wasm2.Frames.Saved) (parent : Wasm2.Frames.Saved)
    (split : savedParents = grandparents ++ [parent]) (instruction : instr) :
    ∃ outer scope, parents = outer ++ [scope] ∧
      ReaderScopeZipperWasm2 outer (scope.advance instruction) grandparents
        (resumedSource parent savedCurrent instruction) := by
  obtain ⟨outer, scope, shape, paired, last⟩ := matched_last (split ▸ same.parents)
  exact ⟨outer, scope, shape, paired, last.resume⟩

/-- Actual Wasm 2 label lookup selects the paired compiler source scope and its full type list. -/
theorem ReaderScopeZipperWasm2.label {parents current savedParents savedCurrent env root st}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (opened : Wasm2.Frames.Open env root st savedParents savedCurrent)
    (depth : Nat) (view : signature.ResultType)
    (selected : Wasm2.labelAt st depth = some view) :
    ∃ scope types, (current :: parents.reverse)[depth]? = some scope ∧
      Wasm2.resolve env view = some types ∧ scope.branchTypes = types.map Translate.valueType := by
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, values⟩ := id opened
  have bound : depth < (savedCurrent :: savedParents.reverse).length := by
    by_contra outside
    have outside' : ¬depth < st.core.ctrls.val.length := by simpa [controls] using outside
    simp [Wasm2.labelAt, outside'] at selected
  have found := List.getElem?_eq_getElem bound
  obtain ⟨scope, scopeFound, matchScope⟩ := same.lookup depth _ found
  have label := opened.labels depth
  rw [selected] at label
  simp only [Wasm2.Frames.labels, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.getElem?_map, found, Option.map_some,
    Option.bind_some] at label
  cases resolved : Wasm2.resolve env view with
  | none => simp [resolved] at label
  | some types =>
    simp only [resolved, Option.map_some, Option.some.injEq, list.mk_list.injEq] at label
    exact ⟨scope, types, scopeFound, rfl, matchScope.branchTypes.trans label.symm⟩

end Itasca.Runtime.Code
