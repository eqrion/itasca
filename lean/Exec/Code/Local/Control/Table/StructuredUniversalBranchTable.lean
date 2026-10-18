import Exec.Code.Local.Control.Table.StructuredUniversalTerminalWithTables
namespace Exec.Code
open Aeneas.Std

/-- Ordered target fragments close one source BR_TABLE. The retained plans and
resolved-code append are syntactic facts produced by the actual table callback. -/
theorem StructuredUniversalPrefixWithTables.branch_table
    {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {jumpTables : List U32} {emit types functions returns locals parents current stack}
    (depths : List labelidx) (fallback : labelidx)
    (invariant : StructuredUniversalPrefixWithTables jumpTables emit before types functions returns locals
      parents current (stack ++ [.I32]))
    (localsEq : compilerLocals after = locals)
    (sites : ∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame)
    (gate : ∀ selector start len, emit (stack ++ [.I32]) (.BR_TABLE depths fallback)
      [.JumpTable selector start len] stack)
    (completion : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
      ∃ previous selector start len suffix,
        FramePlans before.function.code.val.length locals before.frames.val (label :: labels) previous ∧
        resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++ suffix ∧
        BranchTableLayout jumpTables locals (label :: labels) stack (resolvedCode after.function.code.val groups)
          depths fallback before.function.code.val.length after.function.code.val.length selector start len ∧
        before.function.code.val.length + 1 ≤ after.function.code.val.length) :
    StructuredUniversalTerminalWithTables jumpTables emit after types functions returns locals parents
      (current.advance (.BR_TABLE depths fallback)) := by
  refine ⟨localsEq, sites, ?_⟩
  intro label labels groups plans shape parentShapes
  have oldShape : ScopeLabel current label :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  obtain ⟨previous, selector, start, len, suffix, oldPlans, codeEq, table, header⟩ :=
    completion label labels groups plans oldShape parentShapes
  obtain ⟨saved, retained⟩ := invariant.prefixes label labels previous oldPlans oldShape parentShapes
  refine ⟨?_, ?_⟩
  · rw [codeEq]
    exact (saved.extend suffix).advance_current _
  · have prior : StructuredPrefixWithTables (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode after.function.code.val groups) (label :: labels) current.input current.source
        current.bodyPc before.function.code.val.length (stack ++ [.I32]) := by
      rw [codeEq]
      exact retained.extend suffix
    have terminal := StructuredDeadPrefixWithTables.branchTable (types := types) (functions := functions) (returns := returns) (gate selector start len) table header
    simpa only [SourceScope.advance, SourceScope.input] using prior.terminal terminal
end Exec.Code
