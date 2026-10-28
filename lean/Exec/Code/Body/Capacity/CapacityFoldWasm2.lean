import Exec.Code.Body.Reader.Control.ReaderControlEffects
import Exec.Representation.ValidatedStacks
import Exec.Code.Local.Relations.Common.EntryTypedSteps
import Exec.Code.Local.Relations.Control.ControlLayout
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem ValidatedStacksWasm2.head_width {data env ctx index st samples}
    (trace : ValidatedStacksWasm2 data env ctx index st samples) :
    stackWords st.core.vals.val ≤ maximumStackWords samples := by
  cases trace with
  | done => simp [maximumStackWords]
  | step => exact Nat.le_max_left _ _

end Itasca.Runtime.Code
