import Itasca.Runtime.Code.Body.Reader.Control.ReaderScopeFronts
import Itasca.Runtime.Code.Local.Source.SourceStacks
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Entered scopes retain concrete saved operands even when the current
unreachable segment later contains polymorphic stack entries. -/
inductive ScopeConcreteFronts : List SourceScope → List (List code.StackType) → Prop where
  | root : ScopeConcreteFronts [] []
  | push {parents values} (prior : ScopeConcreteFronts parents values)
      (scope : SourceScope) (segment : List code.StackType)
      (known : scope.entered = true → ConcreteStack values.flatten) :
      ScopeConcreteFronts (parents ++ [scope]) (values ++ [segment])

structure ReaderKnownFronts (parents : List SourceScope) (current : SourceScope)
    (values : List (List code.StackType)) : Prop where
  prior : ScopeConcreteFronts parents values
  current : current.entered = true → ConcreteStack values.flatten

theorem ReaderKnownFronts.initial (returns : List valtype) :
    ReaderKnownFronts [] (SourceScope.initial returns) [] := by
  exact ⟨.root, fun _ => by simp [ConcreteStack]⟩

theorem ReaderKnownFronts.advance {parents current values}
    (fronts : ReaderKnownFronts parents current values) (instruction : instr) :
    ReaderKnownFronts parents (current.advance instruction) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderKnownFronts.begin_else {parents current values}
    (fronts : ReaderKnownFronts parents current values)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderKnownFronts parents (current.begin_else bt condition yesExit noEntry normal) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderKnownFronts.push {parents current values}
    (fronts : ReaderKnownFronts parents current values) (child : SourceScope)
    (remaining : List code.StackType)
    (known : child.entered = true → ConcreteStack (values.flatten ++ remaining)) :
    ReaderKnownFronts (parents ++ [current]) child (values ++ [remaining]) := by
  refine ⟨fronts.prior.push current remaining fronts.current, ?_⟩
  simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using known

theorem ScopeConcreteFronts.pop {parents parent values segment}
    (fronts : ScopeConcreteFronts (parents ++ [parent]) (values ++ [segment])) :
    ScopeConcreteFronts parents values ∧ (parent.entered = true → ConcreteStack values.flatten) := by
  generalize scopesEq : parents ++ [parent] = allScopes at fronts
  generalize valuesEq : values ++ [segment] = allValues at fronts
  cases fronts with
  | root => simp at scopesEq
  | @push oldScopes oldValues prior scope actualSegment known =>
    have ss : parents = oldScopes ∧ parent = scope := by simpa using scopesEq
    have vs : values = oldValues ∧ segment = actualSegment := by simpa using valuesEq
    obtain ⟨rfl, rfl⟩ := ss
    obtain ⟨rfl, rfl⟩ := vs
    exact ⟨prior, known⟩

theorem ReaderKnownFronts.pop {parents parent current values segment}
    (fronts : ReaderKnownFronts (parents ++ [parent]) current (values ++ [segment]))
    (instruction : instr) : ReaderKnownFronts parents (parent.advance instruction) values := by
  obtain ⟨prior, known⟩ := fronts.prior.pop
  exact ⟨prior, known⟩
end Itasca.Runtime.Code
