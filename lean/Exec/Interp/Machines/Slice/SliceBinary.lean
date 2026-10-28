import Exec.Interp.Relations.Rel
import Exec.Abs.Sim.Typed

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Binary instructions in the initial proved abstract slice. -/
inductive SliceBinary where
  | add | sub | eq | ltU

def SliceBinary.operation : SliceBinary → Code.IntegerBinary
  | .add => .add | .sub => .sub | .eq => .eq | .ltU => .ltU

end Itasca.Runtime.Interp
