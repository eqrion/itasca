import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.Readback
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Choose whether the local body contract permits divergence. -/
def InvocationWP {α : Type} (allowDivergence : Bool) (run : Result α) (post : α → Prop) : Prop :=
  if allowDivergence then WP.dspec run post else WP.spec run post

end Exec.Interp
