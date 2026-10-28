import Exec.Code.Body.Reader.Control.ReaderScopeZipper
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Every entered child was opened from a monomorphic suspended source parent.
This retains the fact needed when END later restores that parent's stack. -/
inductive ReaderParentReachability {Saved : Type} (poly : Saved → Bool) :
    List SourceScope → SourceScope → List Saved → Prop
  | root (current : SourceScope) : ReaderParentReachability poly [] current []
  | push {parents parent savedParents} (outer : ReaderParentReachability poly parents parent savedParents)
      (savedParent : Saved) (child : SourceScope)
      (entered : child.entered = true → poly savedParent = false) :
      ReaderParentReachability poly (parents ++ [parent]) child (savedParents ++ [savedParent])

theorem ReaderParentReachability.change_current {Saved : Type} {poly : Saved → Bool}
    {parents current savedParents} (chain : ReaderParentReachability poly parents current savedParents)
    (next : SourceScope) (entered : next.entered = current.entered) :
    ReaderParentReachability poly parents next savedParents := by
  cases chain with
  | root => exact .root next
  | push outer savedParent child mono => exact .push outer savedParent next (by simpa [entered] using mono)

theorem ReaderParentReachability.pop {Saved : Type} {poly : Saved → Bool}
    {parents parent child savedParents savedParent}
    (chain : ReaderParentReachability poly (parents ++ [parent]) child (savedParents ++ [savedParent])) :
    ReaderParentReachability poly parents parent savedParents ∧
      (child.entered = true → poly savedParent = false) := by
  generalize sourceEq : parents ++ [parent] = allParents at chain
  generalize savedEq : savedParents ++ [savedParent] = allSaved at chain
  cases chain with
  | root => simp at sourceEq
  | @push outerParents outerParent outerSaved outer stored current entered =>
    have source : parents = outerParents ∧ parent = outerParent := by simpa using sourceEq
    have saved : savedParents = outerSaved ∧ savedParent = stored := by simpa using savedEq
    rcases source with ⟨rfl, rfl⟩
    rcases saved with ⟨rfl, rfl⟩
    exact ⟨outer, entered⟩

/-- Compiler liveness implies a monomorphic active validator frame. The reverse
implication is unnecessary: END can restore a monomorphic dead continuation. -/
structure ReaderReachability {Saved : Type} (poly : Saved → Bool) (reachable : Bool)
    (parents : List SourceScope) (current : SourceScope) (savedParents : List Saved)
    (savedCurrent : Saved) : Prop where
  parents : ReaderParentReachability poly parents current savedParents
  current : reachable = true → poly savedCurrent = false

theorem ReaderReachability.initial {Saved : Type} (poly : Saved → Bool)
    (reachable : Bool) (current : SourceScope) (saved : Saved) (mono : poly saved = false) :
    ReaderReachability poly reachable [] current [] saved := ⟨.root current, fun _ => mono⟩

theorem ReaderReachability.change_current {Saved : Type} {poly : Saved → Bool}
    {reachable parents current savedParents savedCurrent}
    (state : ReaderReachability poly reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (next : SourceScope) (nextSaved : Saved)
    (entered : next.entered = current.entered)
    (mono : nextReachable = true → poly nextSaved = false) :
    ReaderReachability poly nextReachable parents next savedParents nextSaved :=
  ⟨state.parents.change_current next entered, mono⟩

theorem ReaderReachability.push {Saved : Type} {poly : Saved → Bool}
    {reachable parents current savedParents savedCurrent}
    (state : ReaderReachability poly reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (child : SourceScope) (suspended savedChild : Saved)
    (suspendedPoly : poly suspended = poly savedCurrent)
    (entered : child.entered = true → reachable = true)
    (mono : nextReachable = true → poly savedChild = false) :
    ReaderReachability poly nextReachable (parents ++ [current]) child
      (savedParents ++ [suspended]) savedChild := by
  refine ⟨.push state.parents suspended child ?_, mono⟩
  intro live
  rw [suspendedPoly]
  exact state.current (entered live)

theorem ReaderReachability.pop {Saved : Type} {poly : Saved → Bool}
    {reachable parents parent child savedParents savedParent savedCurrent}
    (state : ReaderReachability poly reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr) (resumed : Saved)
    (resumedPoly : poly resumed = poly savedParent)
    (entered : nextReachable = true → child.entered = true) :
    ReaderReachability poly nextReachable parents (parent.advance instruction) savedParents resumed := by
  obtain ⟨outer, parentMono⟩ := state.parents.pop
  refine ⟨outer.change_current _ rfl, ?_⟩
  intro live
  rw [resumedPoly]
  exact parentMono (entered live)

abbrev ReaderReachabilityWasm2 := ReaderReachability (fun saved : Wasm2.Frames.Saved => saved.ctrl.polymorphic_base)
end Itasca.Runtime.Code
