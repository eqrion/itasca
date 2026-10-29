import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalConditional
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- A loop branch has a known literal target and adds no forward fixup. The
static plan derives its liveness and target from the physical LOOP frame. -/
theorem StructuredUniversalPrefix.branch_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count : U32)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (isLoop : frame.kind = .Loop)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count frame.start_pc)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    simpa only [codeEq] using (invariant.sites f member).extend (branchInstructions dst src count frame.start_pc)
  · intro top labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (top :: labels) groups := by
      rw [← framesEq]
      exact plans.before lengthOrder
    obtain ⟨label, guard, labelAt, future⟩ := oldPlans.lookup found position
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have selected := scopeLabels_lookup (List.Forall₂.cons oldShape parentShapes) scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels groups oldPlans oldShape parentShapes).1
    have resolved := resolvedCode_append_code before.function.code.val
      (branchInstructions dst src count frame.start_pc) groups prior.inside
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchInstructions dst src count frame.start_pc)).advance_current (.BR (.mk_uN depth))
    · have fragment : Segment (resolvedCode before.function.code.val groups ++ branchInstructions dst src count frame.start_pc)
          before.function.code.val.length (branchInstructions dst src count label.target)
          after.function.code.val.length := by
        rw [future.loopTarget isLoop]
        exact ⟨resolvedCode before.function.code.val groups, [], by simp,
          resolvedCode_length _ _, by simp [codeEq, resolvedCode_length]⟩
      have terminal := (prior.code.extend (branchInstructions dst src count frame.start_pc)).terminal
        (StructuredDeadPrefix.branch labelAt (future.loopLive isLoop) layout fragment)
      simpa only [codeEq, resolved, SourceScope.advance, SourceScope.input] using terminal

/-- Conditional loop branches preserve the active prefix at their literal
fallthrough coordinate, using the same fixed loop target. -/
theorem StructuredUniversalPrefix.branch_if_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (stack ++ [.I32]))
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count condition resume : U32)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (isLoop : frame.kind = .Loop)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count frame.start_pc condition resume)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals)
    (afterLayout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack)
    (resumePosition : resume.val = after.function.code.val.length) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) stack := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, afterLayout, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    simpa only [codeEq] using (invariant.sites f member).extend (branchIfInstructions dst src count frame.start_pc condition resume)
  · intro top labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (top :: labels) groups := by
      rw [← framesEq]
      exact plans.before lengthOrder
    obtain ⟨label, guard, labelAt, future⟩ := oldPlans.lookup found position
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have selected := scopeLabels_lookup (List.Forall₂.cons oldShape parentShapes) scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels groups oldPlans oldShape parentShapes).1
    have resolved := resolvedCode_append_code before.function.code.val
      (branchIfInstructions dst src count frame.start_pc condition resume) groups prior.inside
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchIfInstructions dst src count frame.start_pc condition resume)).advance_current (.BR_IF (.mk_uN depth))
    · have fragment : Segment (resolvedCode before.function.code.val groups ++ branchIfInstructions dst src count frame.start_pc condition resume)
          before.function.code.val.length (branchIfInstructions dst src count label.target condition resume) resume.val := by
        rw [future.loopTarget isLoop]
        exact ⟨resolvedCode before.function.code.val groups, [], by simp,
          resolvedCode_length _ _, by simp [resumePosition, codeEq, resolvedCode_length]⟩
      have advanced := (prior.code.extend (branchIfInstructions dst src count frame.start_pc condition resume)).append
        (StructuredPrefix.branchIf labelAt (future.loopLive isLoop) layout conditionSlot fragment)
      simpa only [codeEq, resolved, resumePosition, SourceScope.advance, SourceScope.input] using advanced

end Itasca.Runtime.Code
