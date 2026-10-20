import Exec.Code.Local.Checking.FrameExitSlotBounds
import Exec.Code.Local.Coordinates.ScalarSourceCoordinates
import Exec.Code.Local.Callbacks.Common.CompilerMetadataTactic

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every scalar lowerer retains physical frame metadata and only increases
slot capacity. The exact opcode list is shared with callback dispatch coverage. -/
theorem compiler_scalar_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (supported : opcode ∈ sourceCoordinateScalarOpcodes)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    CompilerOrdinaryStable before after := by
  by_cases live : before.reachable = true
  · simp only [sourceCoordinateScalarOpcodes,List.mem_cons,List.not_mem_nil,or_false] at supported
    rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold runtime.compiler.lower.FunctionCompiler.op at called
      rw [if_pos live] at called
      repeat' first | coordinates_head called | metadata_step called using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at called
    rw [if_neg live] at called
    exact compiler_observe_ordinary_result ops law before after state (.Ok ()) called

/-- Ordinary metadata retention preserves all previously recorded result regions. -/
theorem CompilerOrdinaryStable.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) (held : FrameExitSlotBounds before) : FrameExitSlotBounds after :=
  held.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity

end Exec.Code
