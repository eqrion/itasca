import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Interp.Relations.LocalCodePoint

/-!
Slot-prefix preservation for local moves.

Main declarations: `move_prefix`. A direct consumer is `Interp.Machine.Local.ExecutionOwned`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem move_prefix (ty : valtype) (dst src : U32) : PrefixInstruction (Code.move ty dst src) := by
  unfold Code.move
  split
  · exact .copy2 ..
  · exact .copy ..

end Itasca.Runtime.Interp
