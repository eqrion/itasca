import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal

/-!
Sections, each formerly its own module: UniversalBranch, StructuredElseResolvedAppend.
-/

/-! ## UniversalBranch -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem scope_labels_lookup {scopes labels} (shapes : List.Forall₂ ScopeLabel scopes labels)
    {depth : Nat} {scope label} (source : scopes[depth]? = some scope) (target : labels[depth]? = some label) :
    ScopeLabel scope label := by
  induction shapes generalizing depth with
  | nil => simp at source
  | cons shape shapes ih =>
    cases depth with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at source target; subst_vars; exact shape
    | succ depth => exact ih source target

theorem FrameSites.add_branch {code frame} (valid : FrameSites code frame)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (appended : fixups.val = frame.fixups.val ++ [site])
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1)) :
    FrameSites (code ++ branchInstructions dst src count old)
      {frame with end_reachable := true, fixups} := by
  have extended := valid.extend (branchInstructions dst src count old)
  refine ⟨?_, extended.guard⟩
  intro pc member
  simp only [appended, List.mem_append, List.mem_singleton] at member
  rcases member with previous | rfl
  · exact extended.branches pc previous
  · apply Or.inl
    refine ⟨old, ?_⟩
    by_cases elided : count = 0#u32 ∨ src = dst
    · simp [branchInstructions, elided, position]
    · simp [branchInstructions, elided, position, List.getElem?_append]

end Itasca.Runtime.Compiler

end

/-! ## StructuredElseResolvedAppend -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
