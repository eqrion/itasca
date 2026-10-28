import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- An ELSE scope retains its completed then arm, resolved guard, and literal
skip shape. Future branch liveness may overapproximate branches in the then arm;
normal liveness remains the actual decision recorded when ELSE was entered. -/
def StructuredElseEvidence (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (outer : List LabelTarget) (scope : SourceScope) (label : LabelTarget) : Prop :=
  if scope.entered then
    match scope.form with
    | .else_ _ condition yes yesExit noEntry yesNormal =>
      condition.val = slots locals + slots scope.input ∧
      code[scope.entry]? = some (.JumpIfZero condition noEntry) ∧
      StructuredCode emit types functions returns locals code jumpTables
        (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], yesNormal, label.branchLive⟩ :: outer)
        scope.input yes (scope.entry + 1) yesExit (scope.front ++ scope.results) ∧
      IfSkip code yesExit noEntry label.target yesNormal ∧ scope.bodyPc = noEntry.val
    | _ => True
  else True

theorem StructuredElseEvidence.extend {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code outer scope label}
    (evidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer scope label)
    (emitted : List Bytecode) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals (code ++ emitted) outer scope label := by
  unfold StructuredElseEvidence at *
  split at evidence
  · rename_i entered
    simp only [entered, ite_true]
    cases form : scope.form <;> simp only [form] at evidence ⊢
    all_goals try trivial
    obtain ⟨condition, guard, body, skip, begin⟩ := evidence
    exact ⟨condition, fetch_extend guard emitted, body.extend emitted, skip.extend emitted, begin⟩
  · simp_all

theorem StructuredElseEvidence.advance {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code outer scope label}
    (evidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer scope label)
    (instruction : instr) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer (scope.advance instruction) label := by
  simpa only [StructuredElseEvidence, SourceScope.advance, SourceScope.input] using evidence

/-- Completed arms are stored at every active ELSE frame, including suspended
parents. The source and label lists are ordered from innermost to outermost. -/
inductive StructuredElseFrames (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → Prop where
  | nil : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code [] []
  | cons {scopes labels} (scope label)
      (current : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code labels scope label)
      (outer : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code scopes labels) :
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope :: scopes) (label :: labels)

theorem StructuredElseFrames.extend {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code scopes labels}
    (evidence : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code scopes labels) (emitted : List Bytecode) :
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (code ++ emitted) scopes labels := by
  induction evidence with
  | nil => exact .nil
  | cons scope label current outer ih => exact .cons scope label (current.extend emitted) ih

theorem StructuredElseFrames.advance {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code scopes labels scope label}
    (evidence : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope :: scopes) (label :: labels))
    (instruction : instr) :
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope.advance instruction :: scopes) (label :: labels) := by
  cases evidence with
  | cons scope label current outer => exact .cons _ label (current.advance instruction) outer

/-- Completed-arm evidence is uniform over the same future plans as live and
terminal source prefixes. It is a separate syntactic component of the zipper. -/
def StructuredUniversalElse (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop :=
  ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      (current :: parents.reverse) (label :: labels)

theorem StructuredUniversalElse.append {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (emitted : List Bytecode) (instruction : instr)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames = before.frames) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) := by
  intro label labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
    rw [← framesEq]
    exact plans.before order
  have oldShape : ScopeLabel current label :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  have prior := invariant label labels groups oldPlans oldShape parentShapes
  rw [codeEq, resolvedCode_append_code _ _ _ (oldPlans.inside sites)]
  exact (prior.extend emitted).advance instruction

end Itasca.Runtime.Code

