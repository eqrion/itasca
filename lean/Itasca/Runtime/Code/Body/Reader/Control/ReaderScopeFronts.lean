import Itasca.Runtime.Code.Local.Control.Common.UniversalInitial
import Itasca.Runtime.Code.Body.Reader.Control.ReaderScopeZipper
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Saved operand segments determine the exact source prefix below every open
scope. Compiler slot heights alone cannot recover these source types. -/
inductive SourceFronts : List SourceScope → List (List code.StackType) → List code.StackType → Prop where
  | root : SourceFronts [] [] []
  | push {parents values front} (prior : SourceFronts parents values front)
      (scope : SourceScope) (segment : List code.StackType)
      (same : scope.front = Sequence.stackTypes front) :
      SourceFronts (parents ++ [scope]) (values ++ [segment]) (front ++ segment)

theorem SourceFronts.flatten {parents values front} (fronts : SourceFronts parents values front) :
    front = values.flatten := by
  induction fronts with
  | root => rfl
  | push prior scope segment same ih => simp [List.flatten_append, ih]

structure ReaderScopeFronts (parents : List SourceScope) (current : SourceScope)
    (values : List (List code.StackType)) : Prop where
  prior : SourceFronts parents values values.flatten
  current : current.front = Sequence.stackTypes values.flatten

theorem ReaderScopeFronts.initial (returns : List valtype) :
    ReaderScopeFronts [] (SourceScope.initial returns) [] := ⟨.root, rfl⟩

theorem ReaderScopeFronts.advance {parents current values} (fronts : ReaderScopeFronts parents current values)
    (instruction : instr) : ReaderScopeFronts parents (current.advance instruction) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderScopeFronts.begin_else {parents current values} (fronts : ReaderScopeFronts parents current values)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderScopeFronts parents (current.begin_else bt condition yesExit noEntry normal) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderScopeFronts.push {parents current values} (fronts : ReaderScopeFronts parents current values)
    (child : SourceScope) (remaining : List code.StackType)
    (front : child.front = Sequence.stackTypes (values.flatten ++ remaining)) :
    ReaderScopeFronts (parents ++ [current]) child (values ++ [remaining]) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using
      fronts.prior.push current remaining fronts.current
  · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using front

theorem SourceFronts.pop {parents parent values segment front}
    (fronts : SourceFronts (parents ++ [parent]) (values ++ [segment]) front) :
    SourceFronts parents values values.flatten ∧ parent.front = Sequence.stackTypes values.flatten := by
  generalize scopesEq : parents ++ [parent] = allScopes at fronts
  generalize valuesEq : values ++ [segment] = allValues at fronts
  cases fronts with
  | root => simp at scopesEq
  | @push oldScopes oldValues previous prior scope actualSegment same =>
    have ss : parents = oldScopes ∧ parent = scope := by simpa using scopesEq
    have vs : values = oldValues ∧ segment = actualSegment := by simpa using valuesEq
    obtain ⟨rfl, rfl⟩ := ss
    obtain ⟨rfl, rfl⟩ := vs
    exact ⟨prior.flatten ▸ prior, by simpa only [prior.flatten] using same⟩

theorem ReaderScopeFronts.pop {parents parent current values segment}
    (fronts : ReaderScopeFronts (parents ++ [parent]) current (values ++ [segment]))
    (instruction : instr) : ReaderScopeFronts parents (parent.advance instruction) values := by
  obtain ⟨prior, same⟩ := fronts.prior.pop
  exact ⟨prior, same⟩

theorem SourceFronts.prefix {parents values front} (fronts : SourceFronts parents values front)
    (scope : SourceScope) (member : scope ∈ parents) :
    ∃ rest, Sequence.stackTypes front = scope.front ++ rest := by
  induction fronts with
  | root => simp at member
  | @push parents values front prior current segment same ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · obtain ⟨rest, eq⟩ := ih previous
      exact ⟨rest ++ Sequence.stackTypes segment, by
        simp only [Sequence.stackTypes, List.map_append] at *
        simpa only [Sequence.stackTypes, List.append_assoc] using congrArg (fun xs => xs ++ Sequence.stackTypes segment) eq⟩
    · exact ⟨Sequence.stackTypes segment, by simp [Sequence.stackTypes, same]⟩

theorem ReaderScopeFronts.selected {parents current values}
    (fronts : ReaderScopeFronts parents current values) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ rest, current.front = scope.front ++ rest := by
  have member := List.mem_of_getElem? selected
  simp only [List.mem_cons, List.mem_reverse] at member
  rcases member with rfl | member
  · exact ⟨[], by simp⟩
  · obtain ⟨rest, eq⟩ := fronts.prior.prefix scope member
    exact ⟨rest, fronts.current.trans eq⟩

theorem ReaderScopeFronts.branch {parents current values}
    (fronts : ReaderScopeFronts parents current values) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (raw : List code.StackType) (front : List valtype)
    (arguments : Sequence.stackTypes raw = front ++ scope.branchTypes) :
    ∃ discarded, Sequence.stackTypes (values.flatten ++ raw) =
      scope.front ++ discarded ++ scope.branchTypes := by
  obtain ⟨outer, prefixEq⟩ := fronts.selected depth scope selected
  refine ⟨outer ++ front, ?_⟩
  have whole : Sequence.stackTypes (values.flatten ++ raw) =
      current.front ++ Sequence.stackTypes raw := by
    simpa only [Sequence.stackTypes, List.map_append] using
      congrArg (fun xs => xs ++ Sequence.stackTypes raw) fronts.current.symm
  rw [whole, prefixEq, arguments]
  simp only [List.append_assoc]

end Itasca.Runtime.Code
