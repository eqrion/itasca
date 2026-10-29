import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Representation.ValidatedStacks
import Itasca.Runtime.Compiler.Local.Relations.Function.EntryTypedSteps
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem ValidatedStacksWasm2.head_width {data env ctx index st samples}
    (trace : ValidatedStacksWasm2 data env ctx index st samples) :
    stackWords st.core.vals.val ≤ maximumStackWords samples := by
  cases trace with
  | done => simp [maximumStackWords]
  | step => exact Nat.le_max_left _ _

end Itasca.Runtime.Code
