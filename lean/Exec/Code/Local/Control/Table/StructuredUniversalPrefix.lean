import Exec.Code.Local.Control.Table.StructuredPrefixZipper
import Exec.Code.Local.Control.Table.StructuredPrefixEmission
import Exec.Code.Local.Control.Common.UniversalPrefix
namespace Exec.Code
open Aeneas.Std
theorem StructuredParentPrefixes.advance_current {jumpTables : List U32} {emission types functions returns locals code parents labels current}
    (saved : StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code parents labels current)
    (instruction : instr) :
    StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals code parents labels (current.advance instruction) := by
  induction saved with
  | root current => exact .root _
  | push prior label child shape bound saved ih =>
    exact .push prior label (child.advance instruction) shape bound saved

/-- The live prefix invariant is uniform over every admissible future layout.
The source zipper fixes exact label types; the plans supply only future PCs and
exit liveness. This component retains no execution-correctness premise. -/
structure StructuredUniversalPrefix (jumpTables : List U32) (emission : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (stack : List valtype) : Prop where
  localsEq : compilerLocals compiler = locals
  layout : CompilerLayout compiler stack
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredParentPrefixes (jumpTables := jumpTables) emission types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    StructuredPrefix (jumpTables := jumpTables) emission types functions returns locals (resolvedCode compiler.function.code.val groups)
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length stack

theorem StructuredUniversalPrefix.resolved {jumpTables : List U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emission types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emission compiler types functions returns locals parents current stack)
    {label labels groups}
    (plans : FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups)
    (shape : ScopeLabel current label) (parentShapes : List.Forall₂ ScopeLabel parents.reverse labels) :
    StructuredResolvedInv (jumpTables := jumpTables) emission compiler types functions returns locals (label :: labels) groups
      current.input current.source current.bodyPc stack :=
  ⟨invariant.localsEq, invariant.layout, plans.inside invariant.sites,
    (invariant.prefixes label labels groups plans shape parentShapes).2⟩

/-- Actual ordinary emission preserves all possible control completions at
once. A later branch may strengthen liveness or add a fixup without requiring
any earlier ordinary callback to know that future decision. -/
theorem Lowered.structured_universal_advance {jumpTables : List U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emission types functions returns locals parents current stack instruction emitted output}
    (lowered : Lowered before after emitted output)
    (frames : after.frames = before.frames)
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emission before types functions returns locals parents current stack)
    (head : emission stack instruction [emitted] output)
    (ordinary : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emission after types functions returns locals parents (current.advance instruction) output := by
  have codeEq := lowered.1
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by
    simp [codeEq]
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro frame member
    rw [frames] at member
    simpa only [codeEq] using (invariant.sites frame member).extend [emitted]
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val
        (label :: labels) groups := by
      rw [← frames]
      exact plans.before lengthOrder
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have old := invariant.resolved oldPlans oldShape parentShapes
    have next := lowered.structured_resolved_advance old head ordinary
    have saved := (invariant.prefixes label labels groups oldPlans oldShape parentShapes).1
    have resolved := resolvedCode_append_code before.function.code.val [emitted] groups old.inside
    refine ⟨?_, next.code⟩
    simpa only [codeEq, resolved] using (saved.extend [emitted]).advance_current instruction

end Exec.Code
