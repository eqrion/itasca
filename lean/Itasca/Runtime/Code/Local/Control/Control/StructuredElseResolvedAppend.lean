import Itasca.Runtime.Code.Local.Control.Table.StructuredElseEvidence
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- A callback may change relocation lists while preserving the resolved
prefix under the corresponding previous plans. Completed ELSE arms follow
that same syntactic prefix, independent of the newly emitted fragments. -/
theorem StructuredUniversalElse.resolved_append
    {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {jumpTables : List U32} {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse jumpTables emit before types functions returns locals parents current)
    (instruction : instr)
    (completion : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
      ∃ previous suffix,
        FramePlans before.function.code.val.length locals before.frames.val (label :: labels) previous ∧
        resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++ suffix) :
    StructuredUniversalElse jumpTables emit after types functions returns locals parents
      (current.advance instruction) := by
  intro label labels groups plans shape parentShapes
  have oldShape : ScopeLabel current label :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  obtain ⟨previous, suffix, oldPlans, codeEq⟩ := completion label labels groups plans oldShape parentShapes
  have prior := invariant label labels previous oldPlans oldShape parentShapes
  rw [codeEq]
  exact (prior.extend suffix).advance instruction
end Itasca.Runtime.Code
