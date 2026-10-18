import Exec.Code.Local.Callbacks.Control.ElseEvidence
import Exec.Code.Local.Callbacks.Common.ParentPrefixChange
namespace Exec.Code
open Aeneas.Std

/-- The source cursor at ELSE remembers the completed then arm and resumes an
empty else body at the freshly resolved guard destination. -/
def SourceScope.begin_else (scope : SourceScope) (bt : blocktype) (condition : U32)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) : SourceScope :=
  { scope with form := .else_ bt condition scope.source yesExit noEntry normal, source := [], bodyPc := noEntry.val }

theorem SourceScope.begin_else_arguments (scope : SourceScope) (bt : blocktype) (condition : U32)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) (form : scope.form = .then_ bt condition) :
    (scope.begin_else bt condition yesExit noEntry normal).arguments = scope.arguments := by
  simp [SourceScope.begin_else, SourceScope.arguments, SourceScope.input, form]

theorem ScopeLabel.before_else {scope bt condition yesExit noEntry normal label}
    (shape : ScopeLabel (scope.begin_else bt condition yesExit noEntry normal) label)
    (form : scope.form = .then_ bt condition) : ScopeLabel scope label := by
  refine ⟨shape.front, ?_, shape.results⟩
  simpa [SourceScope.begin_else, SourceScope.branchTypes, form] using shape.branchTypes

theorem ElseFrames.outer {types functions returns locals code scopes labels scope label}
    (frames : ElseFrames types functions returns locals code (scope :: scopes) (label :: labels)) :
    ElseFrames types functions returns locals code scopes labels := by
  cases frames with
  | cons _ _ _ outer => exact outer

theorem ElseEvidence.begin_else {types functions returns locals outer bt yesExit normal}
    {code : List Bytecode} {scope : SourceScope} {label : LabelTarget} {condition noEntry : U32}
    (entered : scope.entered = true)
    (conditionSlot : condition.val = slots locals + slots scope.input)
    (guard : code[scope.entry]? = some (.JumpIfZero condition noEntry))
    (body : CodeRel types functions returns locals code
      (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], normal, label.branchLive⟩ :: outer)
      scope.input scope.source (scope.entry + 1) yesExit (scope.front ++ scope.results))
    (skip : IfSkip code yesExit noEntry label.target normal) :
    ElseEvidence types functions returns locals code outer
      (scope.begin_else bt condition yesExit noEntry normal) label := by
  simp only [ElseEvidence, SourceScope.begin_else, entered, ite_true]
  exact ⟨conditionSlot, guard, body, skip, trivial⟩

end Exec.Code
