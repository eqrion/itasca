import Exec.Code.Local.Relations.Common.FutureFrames
namespace Exec.Code
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

theorem SuspendedTerminal.full {types functions returns locals code labels before source start cursor}
    (saved : SuspendedTerminal types functions returns locals code labels before source start cursor) :
    DeadCodePrefix types functions returns locals code labels before source start cursor := by
  simpa only [List.take_append_drop] using saved.2.extend (code.drop cursor)

theorem SuspendedTerminal.stable {types functions returns locals code labels before source start cursor}
    (saved : SuspendedTerminal types functions returns locals code labels before source start cursor)
    (changed : List Bytecode) (bound : cursor ≤ changed.length)
    (same : changed.take cursor = code.take cursor) :
    SuspendedTerminal types functions returns locals changed labels before source start cursor :=
  ⟨bound, same ▸ saved.2⟩

theorem SuspendedTerminal.extend {types functions returns locals code labels before source start cursor}
    (saved : SuspendedTerminal types functions returns locals code labels before source start cursor)
    (emitted : List Bytecode) :
    SuspendedTerminal types functions returns locals (code ++ emitted) labels before source start cursor := by
  have bound := saved.1
  exact saved.stable (code ++ emitted) (by simp; omega) (List.take_append_of_le_length bound)

theorem DeadCodePrefix.suspend {types functions returns locals code labels before source start}
    (current : DeadCodePrefix types functions returns locals code labels before source start code.length) :
    SuspendedTerminal types functions returns locals code labels before source start code.length :=
  ⟨Nat.le_refl _, by simpa using current⟩

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

theorem ParentPrefix.extend {types functions returns locals code labels parent child}
    (saved : ParentPrefix types functions returns locals code labels parent child)
    (emitted : List Bytecode) :
    ParentPrefix types functions returns locals (code ++ emitted) labels parent child := by
  unfold ParentPrefix at *
  split at saved
  · split at saved
    · simpa only [‹parent.entered = true›, ‹child.entered = true›, ite_true] using saved.extend emitted
    · simpa only [‹parent.entered = true›, ‹¬child.entered = true›, ite_true, ite_false, Bool.false_eq_true] using saved.extend emitted
  · simp_all

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

theorem ParentPrefixes.extend {types functions returns locals code parents labels current}
    (saved : ParentPrefixes types functions returns locals code parents labels current)
    (emitted : List Bytecode) :
    ParentPrefixes types functions returns locals (code ++ emitted) parents labels current := by
  induction saved with
  | root current => exact .root current
  | push prior label child shape bound saved ih =>
    exact .push ih label child shape (by simp; omega) (saved.extend emitted)


/-- Terminal evidence remains valid when the physical builder advances past
an unentered source subtree. The logical continuation cannot precede it. -/
theorem DeadCodePrefix.delay {types functions returns locals code labels before source start cursor}
    (current : DeadCodePrefix types functions returns locals code labels before source start cursor)
    {later : Nat} (order : cursor ≤ later) :
    DeadCodePrefix types functions returns locals code labels before source start later := by
  intro suffix tail next final nextOrder bound
  exact current suffix tail next final (order.trans nextOrder) bound

theorem SuspendedTerminal.close_child {types functions returns locals code labels before source start cursor}
    (saved : SuspendedTerminal types functions returns locals code labels before source start cursor)
    (instruction : instr) :
    DeadCodePrefix types functions returns locals code labels before (source ++ [instruction]) start code.length :=
  (saved.full.skip_source [instruction]).delay saved.1

theorem ParentPrefix.resume {types functions returns locals code labels parent child}
    (saved : ParentPrefix types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    {source next stack}
    (closed : CodePrefix types functions returns locals code labels child.arguments source child.entry next stack) :
    CodePrefix types functions returns locals code labels parent.input (parent.source ++ source)
      parent.bodyPc next stack := by
  simp only [ParentPrefix, parentEntered, childEntered, ite_true] at saved
  exact saved.resume closed

theorem ParentPrefix.resume_dead {types functions returns locals code labels parent child}
    (saved : ParentPrefix types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    {source next}
    (closed : DeadCodePrefix types functions returns locals code labels child.arguments source child.entry next) :
    DeadCodePrefix types functions returns locals code labels parent.input (parent.source ++ source)
      parent.bodyPc next := by
  simp only [ParentPrefix, parentEntered, childEntered, ite_true] at saved
  exact saved.resume_dead closed

theorem ParentPrefix.close_unentered {types functions returns locals code labels parent child}
    (saved : ParentPrefix types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = false)
    (instruction : instr) :
    DeadCodePrefix types functions returns locals code labels parent.input (parent.source ++ [instruction])
      parent.bodyPc code.length := by
  simp only [ParentPrefix, parentEntered, childEntered, Bool.false_eq_true, ite_true, ite_false] at saved
  exact saved.close_child instruction

end Exec.Code
