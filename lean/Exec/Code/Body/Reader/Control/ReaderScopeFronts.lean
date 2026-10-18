import Exec.Code.Local.Control.Common.UniversalInitial
import Exec.Code.Body.Reader.Control.ReaderScopeZipper
namespace Exec.Code
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

theorem SourceFronts.length {parents values front} (fronts : SourceFronts parents values front) :
    parents.length = values.length := by
  induction fronts <;> simp_all

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

theorem SourceFronts.lookup {parents values front} (fronts : SourceFronts parents values front)
    (index : Nat) (scope : SourceScope) (found : parents[index]? = some scope) :
    scope.front = Sequence.stackTypes (values.take index).flatten := by
  induction fronts with
  | root => simp at found
  | @push parents values front prior current segment same ih =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    by_cases earlier : index < parents.length
    · have atIndex : parents[index]? = some scope := by
        simpa only [List.getElem?_append, if_pos earlier] using found
      have short : index ≤ values.length := by rw [← prior.length]; omega
      simpa only [List.take_append_of_le_length short] using ih atIndex
    · have last : index = parents.length := by simp only [List.length_append, List.length_singleton] at bound; omega
      have equal : current = scope := by simpa only [last, List.getElem?_append, lt_self_iff_false,
        if_false, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] using found
      subst scope
      rw [last, prior.length, List.take_append_of_le_length (Nat.le_refl values.length), List.take_length]
      simpa only [prior.flatten] using same

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

end Exec.Code
