import Itasca.Runtime.Compiler.Local.Control.Table.StructuredElseEvidence
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredParentPrefixChange
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseSource
namespace Itasca.Runtime.Code
open Aeneas.Std
theorem StructuredElseFrames.outer {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code scopes labels scope label}
    (frames : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope :: scopes) (label :: labels)) :
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code scopes labels := by
  cases frames with
  | cons _ _ _ outer => exact outer

theorem StructuredElseEvidence.begin_else {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals outer bt yesExit normal}
    {code : List Bytecode} {scope : SourceScope} {label : LabelTarget} {condition noEntry : U32}
    (entered : scope.entered = true)
    (conditionSlot : condition.val = slots locals + slots scope.input)
    (guard : code[scope.entry]? = some (.JumpIfZero condition noEntry))
    (body : StructuredCode emit types functions returns locals code jumpTables
      (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], normal, label.branchLive⟩ :: outer)
      scope.input scope.source (scope.entry + 1) yesExit (scope.front ++ scope.results))
    (skip : IfSkip code yesExit noEntry label.target normal) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer
      (scope.begin_else bt condition yesExit noEntry normal) label := by
  simp only [StructuredElseEvidence, SourceScope.begin_else, entered, ite_true]
  exact ⟨conditionSlot, guard, body, skip, trivial⟩

end Itasca.Runtime.Code

