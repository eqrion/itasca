import Exec.Code.Local.Checking.OpenInstructionCompiler
import Exec.Code.Local.Lowering.Common.NumericInstructionPublication
import Exec.Code.Local.Lowering.Table.ScalarTablePreservation

namespace Exec.Code
open Aeneas Aeneas.Std Abs.Numeric

/-- Observation preserves every instruction's operand check and pending branch
owner, including in an unreachable source region. -/
theorem compiler_observe_open_instructions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : CompilerInstructionPrefix before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  have stable := compiler_observe_stable ops law before after state called
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have growth : InstructionCheckExtends before.function after.function := by
    refine ⟨stable.capacity,?_,?_,?_,?_,?_⟩ <;> rw [frame] <;> exact le_rfl
  have same : after.function.code.val = before.function.code.val := by rw [frame]
  refine held.append growth ?_ [] (by simpa using same) (by simp)
  intro index owned
  have frames : after.frames = before.frames := by rw [frame]
  simpa only [PendingInstructionSite,frames] using owned

end Exec.Code
