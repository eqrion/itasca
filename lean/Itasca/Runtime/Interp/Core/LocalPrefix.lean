import Itasca.Runtime.Interp.Core.LocalInversion
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Interp.Relations.LocalCodePoint
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem move_prefix (ty : valtype) (dst src : U32) : PrefixInstruction (Code.move ty dst src) := by
  unfold Code.move
  split
  · exact .copy2 ..
  · exact .copy ..

end Itasca.Runtime.Interp
