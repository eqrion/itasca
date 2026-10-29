import Itasca.Runtime.Compiler.Local.Relations.Prefix.FutureFrames

/-!
Source control information retained while callbacks are still reading the body. ELSE remembers the completed arm and the actual skip decision.

Main declarations: `ScopeForm` and `ScopeForm.kind`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Source control information retained while callbacks are still reading the
body. ELSE remembers the completed arm and the actual skip decision. -/
inductive ScopeForm where
  | body
  | block (type : blocktype)
  | loop (type : blocktype)
  | then_ (type : blocktype) (condition : U32)
  | else_ (type : blocktype) (condition : U32) (yes : List instr)
      (yesExit : Nat) (noEntry : U32) (yesNormal : Bool)

def ScopeForm.kind : ScopeForm → Itasca.code.LabelKind
  | .body => .Body
  | .block _ => .Block
  | .loop _ => .Loop
  | .then_ _ _ => .Then
  | .else_ _ _ _ _ _ _ => .Else

structure SourceScope where
  form : ScopeForm
  front : List valtype
  params : List valtype
  results : List valtype
  source : List instr
  entry : Nat
  bodyPc : Nat
  entered : Bool

def SourceScope.input (scope : SourceScope) : List valtype := scope.front ++ scope.params

def SourceScope.arguments (scope : SourceScope) : List valtype :=
  scope.input ++ match scope.form with | .then_ _ _ | .else_ _ _ _ _ _ _ => [.I32] | _ => []

def SourceScope.branchTypes (scope : SourceScope) : List valtype :=
  match scope.form with | .loop _ => scope.params | _ => scope.results

/-- The source zipper fixes label types, while a future plan supplies only
coordinates and liveness. Equal word widths cannot substitute for these types. -/
structure ScopeLabel (scope : SourceScope) (label : LabelTarget) : Prop where
  front : label.front = scope.front
  branchTypes : label.branchTypes = scope.branchTypes
  results : label.resultTypes = scope.results

/-- A terminal suspended parent owns just the code before its child, exactly
as a live suspended parent does. No instruction in an unentered child is needed. -/
def SuspendedTerminal (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) : Prop :=
  cursor ≤ code.length ∧ DeadCodePrefix types functions returns locals (code.take cursor)
    labels before source start cursor

/-- A parent either waits for an entered child's typed result, already has a
terminal prefix, or itself belongs to an unentered source subtree. -/
def ParentPrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (parent child : SourceScope) : Prop :=
  if parent.entered then
    if child.entered then
      SuspendedPrefix types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry child.arguments
    else SuspendedTerminal types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry
  else True

/-- The saved parent chain mirrors the source validator zipper. Each parent
owns its prefix before the next child's opening instruction. -/
inductive ParentPrefixes (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → SourceScope → Prop where
  | root (current) : ParentPrefixes types functions returns locals code [] [] current
  | push {parents labels parent} (prior : ParentPrefixes types functions returns locals code parents labels parent)
      (label child) (shape : ScopeLabel parent label)
      (bound : child.entry ≤ code.length)
      (saved : ParentPrefix types functions returns locals code (label :: labels) parent child) :
      ParentPrefixes types functions returns locals code (parents ++ [parent]) (label :: labels) child

end Itasca.Runtime.Compiler
