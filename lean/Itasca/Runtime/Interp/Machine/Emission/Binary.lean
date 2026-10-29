import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.SourceMachine.Sim.Typed

/-!
Binary instructions in the initial proved abstract slice.

Main declarations: `SliceBinary` and `SliceBinary.operation`. A direct consumer is `Interp.Machine.Emission.Opcode`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Binary instructions in the initial proved abstract slice. -/
inductive SliceBinary where
  | add | sub | eq | ltU

def SliceBinary.operation : SliceBinary → Code.IntegerBinary
  | .add => .add | .sub => .sub | .eq => .eq | .ltU => .ltU

end Itasca.Runtime.Interp
