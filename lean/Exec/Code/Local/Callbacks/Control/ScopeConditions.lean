import Exec.Code.Local.Control.Common.UniversalInitial
import Exec.Code.Local.Callbacks.Control.ElseSource
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The saved IF condition occupies the word immediately above its parameters.
Its exact coordinate is retained while either arm is compiled. -/
def ScopeCondition (locals : List valtype) (scope : SourceScope) : Prop :=
  match scope.form with
  | .then_ _ condition | .else_ _ condition _ _ _ _ =>
      scope.entered = true → condition.val = slots locals + slots scope.input
  | _ => True

def ScopeConditions (locals : List valtype) (parents : List SourceScope) (current : SourceScope) : Prop :=
  ∀ scope ∈ parents ++ [current], ScopeCondition locals scope

theorem ScopeCondition.advance {locals scope} (condition : ScopeCondition locals scope)
    (instruction : instr) : ScopeCondition locals (scope.advance instruction) := condition

theorem ScopeCondition.begin_else {locals scope} (condition : ScopeCondition locals scope)
    (bt : blocktype) (operand : U32) (form : scope.form = .then_ bt operand)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ScopeCondition locals (scope.begin_else bt operand yesExit noEntry normal) := by
  simpa only [ScopeCondition, form, SourceScope.begin_else, SourceScope.input] using condition

theorem ScopeConditions.current {locals parents current} (conditions : ScopeConditions locals parents current) :
    ScopeCondition locals current := conditions current (by simp)

theorem ScopeConditions.replace_current {locals parents current}
    (conditions : ScopeConditions locals parents current) (next : SourceScope) (condition : ScopeCondition locals next) :
    ScopeConditions locals parents next := by
  intro scope member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact conditions scope (List.mem_append_left _ member)
  · exact condition

theorem ScopeConditions.advance {locals parents current} (conditions : ScopeConditions locals parents current)
    (instruction : instr) : ScopeConditions locals parents (current.advance instruction) :=
  conditions.replace_current _ (conditions.current.advance instruction)

theorem ScopeConditions.begin_else {locals parents current} (conditions : ScopeConditions locals parents current)
    (bt : blocktype) (operand : U32) (form : current.form = .then_ bt operand)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ScopeConditions locals parents (current.begin_else bt operand yesExit noEntry normal) :=
  conditions.replace_current _ (conditions.current.begin_else bt operand form yesExit noEntry normal)

theorem ScopeConditions.push {locals parents current} (conditions : ScopeConditions locals parents current)
    (child : SourceScope) (condition : ScopeCondition locals child) :
    ScopeConditions locals (parents ++ [current]) child := by
  intro scope member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (old | rfl) | rfl
  · exact conditions scope (by simp [old])
  · exact conditions.current
  · exact condition

theorem ScopeConditions.pop {locals parents parent current}
    (conditions : ScopeConditions locals (parents ++ [parent]) current) : ScopeConditions locals parents parent := by
  intro scope member
  exact conditions scope (List.mem_append_left _ member)

theorem ScopeConditions.initial {locals returns} : ScopeConditions locals [] (SourceScope.initial returns) := by
  intro scope member
  simp only [List.nil_append, List.mem_singleton] at member
  subst scope
  trivial

end Itasca.Runtime.Code
