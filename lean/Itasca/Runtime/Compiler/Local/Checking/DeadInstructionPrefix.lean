import Itasca.Runtime.Compiler.Local.Checking.BranchCallbackInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.BranchCallbackExitSlots

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Every dead ordinary lowerer observes without changing code or frames.
Both maintained invariants survive independently of the opcode or immediates. -/
theorem compiler_dead_op_checked_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have checked := compiler_dead_op_open_instructions ops law before after state opcode a b bits dead held called
  unfold runtime.compiler.lower.FunctionCompiler.op at called
  rw [if_neg (by simp [dead])] at called
  exact ⟨checked,compiler_observe_exit_slots ops law before after state exits called⟩

end Itasca.Runtime.Code
