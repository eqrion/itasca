import Itasca.Runtime.Code.Local.Control.Table.StructuredUniversalPrefix
import Itasca.Runtime.Code.Local.Lowering.Common.LoweringEmpty
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Instructions with no emitted bytecode advance every possible structured
completion while retaining all pending fixups and parent prefixes. -/
theorem LoweredEmpty.structured_universal_advance {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack instruction output}
    (lowered : LoweredEmpty before after output) (frames : after.frames = before.frames)
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (head : emit stack instruction [] output)
    (notTable : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) output := by
  have codeEq := lowered.1
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro frame member
    simpa only [codeEq] using invariant.sites frame (by simpa only [frames] using member)
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      simpa only [codeEq, frames] using plans
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    obtain ⟨saved, prefixCode⟩ := invariant.prefixes label labels groups oldPlans oldShape parentShapes
    have fragment : Segment (resolvedCode before.function.code.val groups) before.function.code.val.length []
        before.function.code.val.length := ⟨resolvedCode before.function.code.val groups, [], by simp, by simp [resolvedCode_length], by simp⟩
    have advanced := prefixCode.append (StructuredPrefix.linear head notTable fragment)
    exact ⟨by simpa only [codeEq] using saved.advance_current instruction,
      by simpa only [codeEq, SourceScope.advance, SourceScope.input] using advanced⟩

end Itasca.Runtime.Code

