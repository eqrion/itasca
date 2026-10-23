import Exec.Interp.Core.LocalInversion
import Exec.Interp.Relations.PrefixDispatch
import Exec.Interp.Relations.LocalCodePoint
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem move_prefix (ty : valtype) (dst src : U32) : PrefixInstruction (Code.move ty dst src) := by
  unfold Code.move
  split
  · exact .copy2 ..
  · exact .copy ..

end Exec.Interp
