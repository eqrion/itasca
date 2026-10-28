import Exec.Store.Initialization.SegmentLoopSource
import Exec.Interp.Relations.Synthetic

namespace Exec.Store
open Aeneas Aeneas.Std SpecExt
open Exec.Interp

/-- Segment execution can fail only at a memory or table range check. -/
def SegmentExecutionStatus {T : Type} (result : core.result.Result T runtime.ExecError) : Prop :=
  match result with
  | .Ok _ => True
  | .Err error => error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds

end Exec.Store
