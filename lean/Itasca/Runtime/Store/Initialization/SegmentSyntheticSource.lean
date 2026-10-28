import Itasca.Runtime.Store.Initialization.SegmentLoopSource
import Itasca.Runtime.Interp.Relations.Synthetic

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Interp

/-- Segment execution can fail only at a memory or table range check. -/
def SegmentExecutionStatus {T : Type} (result : core.result.Result T runtime.ExecError) : Prop :=
  match result with
  | .Ok _ => True
  | .Err error => error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds

end Itasca.Runtime.Store
