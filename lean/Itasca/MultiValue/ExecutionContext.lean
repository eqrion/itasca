import Itasca.MultiValue.Execution
import Itasca.MultiValue.StepContext

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Return typing is supplied by the selected signature descriptor, so the
semantic result context can be erased to the runtime's scalar context. -/
theorem Execution.change_context {data env ctx index st final}
    (h : Execution data env ctx index st final) (ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) : Execution data env ctx' index st final := by
  induction h with
  | nil st => exact .nil st
  | cons st next last opcode pos hc hr hs _ ih =>
    exact .cons st next last opcode pos hc hr
      ((step_context _ data env ctx ctx' index opcode hlocals).symm.trans hs) ih

end Itasca.MultiValue
