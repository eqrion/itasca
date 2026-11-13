import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards

/-!
Sections, each formerly its own module: ElseEvidence, ElseSource, ElseFrames.
-/

/-! ## ElseEvidence -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- An ELSE scope retains its completed then arm, resolved guard, and literal
skip shape. Future branch liveness may overapproximate branches in the then arm;
normal liveness remains the actual decision recorded when ELSE was entered. -/
def ElseEvidence (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (outer : List LabelTarget) (scope : SourceScope) (label : LabelTarget) : Prop :=
  if scope.entered then
    match scope.form with
    | .else_ _ condition yes yesExit noEntry yesNormal =>
      condition.val = slots locals + slots scope.input ∧
      code[scope.entry]? = some (.JumpIfZero condition noEntry) ∧
      CodeRel types functions returns locals code
        (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], yesNormal, label.branchLive⟩ :: outer)
        scope.input yes (scope.entry + 1) yesExit (scope.front ++ scope.results) ∧
      IfSkip code yesExit noEntry label.target yesNormal ∧ scope.bodyPc = noEntry.val
    | _ => True
  else True

/-- Completed arms are stored at every active ELSE frame, including suspended
parents. The source and label lists are ordered from innermost to outermost. -/
inductive ElseFrames (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → Prop where
  | nil : ElseFrames types functions returns locals code [] []
  | cons {scopes labels} (scope label)
      (current : ElseEvidence types functions returns locals code labels scope label)
      (outer : ElseFrames types functions returns locals code scopes labels) :
      ElseFrames types functions returns locals code (scope :: scopes) (label :: labels)

/-- Completed-arm evidence is uniform over the same future plans as live and
terminal source prefixes. It is a separate syntactic component of the zipper. -/
def UniversalElse {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop :=
  ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    ElseFrames types functions returns locals (resolvedCode compiler.function.code.val groups)
      (current :: parents.reverse) (label :: labels)

end Itasca.Runtime.Compiler

end

/-! ## ElseSource -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## ElseFrames -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

def ScopeForm.isElse : ScopeForm → Bool
  | .else_ _ _ _ _ _ _ => true
  | _ => false

theorem ElseEvidence.fresh {types functions returns locals code labels child label}
    (fresh : child.form.isElse = false) :
    ElseEvidence types functions returns locals code labels child label := by
  unfold ElseEvidence
  split
  · cases form : child.form <;> simp_all [ScopeForm.isElse]
  · trivial

end Itasca.Runtime.Compiler

end
