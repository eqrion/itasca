import Itasca.Runtime.Interp.Relations.FrameStack
import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.Interp.Calls.ReturnRefinement

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The compiler's code-length certificate rules out PC increment overflow
whenever the interpreter fetches an actual instruction. -/
theorem FrameProgram.fetched_bound {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions} (program : FrameProgram store raw compiled locals results functions)
    (instruction : runtime.bytecode.Instr)
    (fetched : compiled.code.val[raw.pc.val]? = some instruction) : raw.pc.val < U32.max := by
  have bound := (List.getElem?_eq_some_iff.mp fetched).1
  exact lt_of_lt_of_le bound program.fetchBound

end Itasca.Runtime.Interp
