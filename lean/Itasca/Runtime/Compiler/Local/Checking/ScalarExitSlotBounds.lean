import Itasca.Runtime.Compiler.Local.Checking.FrameExitSlotBounds
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarSourceCoordinates
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Ordinary metadata retention preserves all previously recorded result regions. -/
theorem CompilerOrdinaryStable.exit_slots {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) (held : FrameExitSlotBounds before) : FrameExitSlotBounds after :=
  held.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity

end Itasca.Runtime.Compiler
