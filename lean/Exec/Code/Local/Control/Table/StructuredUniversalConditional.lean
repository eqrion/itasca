import Exec.Code.Local.Control.Table.StructuredUniversalBranch
import Exec.Code.Local.Control.Table.StructuredResolvedConditionalPrefix
import Exec.Code.Local.Control.Common.UniversalConditional
namespace Exec.Code
open Aeneas.Std
theorem StructuredUniversalPrefix.branch_if_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (stack ++ [.I32]))
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 2))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count old condition resume)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (localsEq : compilerLocals after = locals) (afterLayout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack)
    (resumePosition : resume.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 1 else 3)) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) stack := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, afterLayout, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_or_eq_of_mem_set member with previous | rfl
    · simpa only [codeEq] using (invariant.sites f previous).extend (branchIfInstructions dst src count old condition resume)
    · have frameOk := invariant.sites frame (List.mem_of_getElem? found)
      simpa only [codeEq] using frameOk.add_conditional dst src count old condition resume site fixups appended sitePosition
  · intro top labels groups plans shape parentShapes
    obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
      plans.before_mark fixups framesEq found position
    have oldPlans := priorPlans.before lengthOrder
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have allShapes : List.Forall₂ ScopeLabel (current :: parents.reverse) (top :: labels) :=
      .cons oldShape parentShapes
    have selected := scopeLabels_lookup allShapes scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels _ oldPlans oldShape parentShapes).1
    have resolved := resolvedCode_new_br_if before.function.code.val earlier suffix
      ⟨frame.fixups.val, label.target⟩ dst src count old condition resume site sitePosition prior.inside
    have terminal := prior.code.resolved_branchIf (old := old) prior.inside sitePosition resumePosition labelAt live rfl layout conditionSlot
    rw [grouped, appended]
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchIfInstructions dst src count label.target condition resume)).advance_current (.BR_IF (.mk_uN depth))
    · by_cases elided : count = 0#u32 ∨ src = dst
      all_goals simpa [codeEq, SourceScope.advance, SourceScope.input, branchIfInstructions, elided, resumePosition] using terminal

end Exec.Code
