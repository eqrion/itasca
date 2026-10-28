import Itasca.Runtime.Code.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Code.Local.Checking.ElseCallbackInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source THEN geometry provides the owned guard needed by actual ELSE in
live, terminated, and unentered arms. -/
theorem StructuredCompilerPrefix.else_open_instructions {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {jumpTables emit initial compiler after types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (sourceBt : blocktype) (condition : U32)
    (form : current.form = .then_ sourceBt condition) (bt : signature.BlockType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (held : CompilerInstructionPrefix compiler)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have liveGuard : compiler.reachable = true → frame.if_pc ≠ none := by
    intro live absent
    have entered := (invariant.live live).1
    have guard := shape.guard
    simp [absent,form,SourceScope.guardPosition,entered] at guard
  have owned : ∀ guard, frame.if_pc = some guard → ∃ operand,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero operand core.num.U32.MAX) := by
    intro guard selected
    have same := shape.guard
    simp only [selected,Option.map_some,form,SourceScope.guardPosition] at same
    cases entered : current.entered with
    | false => simp [entered] at same
    | true =>
      have position : guard.val = current.entry := by simpa [entered] using same
      refine ⟨condition,?_⟩
      rw [position]
      have entry : current.entered = true → compiler.function.code.val[current.entry]? =
          some (.JumpIfZero condition core.num.U32.MAX) := by
        simpa [ScopeEntryCode,form] using shape.entryCode
      exact entry entered
  apply compiler_else_open_instructions ops law compiler after state bt frame prior frames owned ?_ ?_ held called
  · intro absent
    by_cases live : compiler.reachable = true
    · exact False.elim (liveGuard live absent)
    · cases reachable : compiler.reachable <;> simp_all
  · have room := invariant.codeBudget
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac

end Itasca.Runtime.Code
