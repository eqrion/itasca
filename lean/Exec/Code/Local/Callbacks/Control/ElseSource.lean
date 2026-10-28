import Exec.Code.Local.Callbacks.Control.ElseEvidence
import Exec.Code.Local.Relations.Common.PrefixZipper
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
