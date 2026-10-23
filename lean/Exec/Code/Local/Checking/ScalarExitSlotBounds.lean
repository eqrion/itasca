import Exec.Code.Local.Checking.FrameExitSlotBounds
import Exec.Code.Local.Coordinates.ScalarSourceCoordinates
import Exec.Code.Local.Callbacks.Common.CompilerMetadataTactic

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Ordinary metadata retention preserves all previously recorded result regions. -/
theorem CompilerOrdinaryStable.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) (held : FrameExitSlotBounds before) : FrameExitSlotBounds after :=
  held.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity

end Exec.Code
