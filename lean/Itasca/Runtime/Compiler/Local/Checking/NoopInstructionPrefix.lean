import Itasca.Runtime.Compiler.Local.Checking.NumericInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.BranchCallbackExitSlots

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- NOP and DROP perform only the final operand observation on both live and
dead paths. They preserve all instruction and recorded exit-slot checks. -/
theorem compiler_nop_drop_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (drop : Bool)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (if drop then 26#u16 else 1#u16)
      0#u32 0#u32 0#u128 = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops before state
      (if drop then 26#u16 else 1#u16) 0#u32 0#u32 0#u128 = runtime.compiler.FunctionCompiler.observe ops before state := by
    cases drop <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> split <;> rfl
  rw [dispatch] at called
  exact ⟨compiler_observe_open_instructions ops law before after state held called,
    compiler_observe_exit_slots ops law before after state exits called⟩

end Itasca.Runtime.Code
