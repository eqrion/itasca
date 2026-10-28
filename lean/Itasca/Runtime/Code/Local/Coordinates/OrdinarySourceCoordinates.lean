import Itasca.Runtime.Code.Local.Coordinates.SourceCoordinateCallbacks
import Itasca.Runtime.Code.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Code.Local.Capacity.MemoryAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Dead ordinary instructions only advance the observed source cursor. -/
theorem compiler_dead_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : SourceCoordinates before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  unfold runtime.compiler.lower.FunctionCompiler.op at called
  rw [if_neg (by simp [dead])] at called
  exact compiler_observe_source_coordinates ops law before after state held forward called

end Itasca.Runtime.Code
