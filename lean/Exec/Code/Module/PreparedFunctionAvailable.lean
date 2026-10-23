import Exec.Code.Module.PreparedExecutableSafety
import Exec.Code.Local.Capacity.IndependentBodyReplay
import Exec.Code.Body.Reader.Acceptance.SourceStepAcceptanceWasm2
import Exec.Code.Body.Reader.Source.SourceBudgetAdvance
import Exec.Code.Module.PreparedFunctionDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Source-derived conservative total charges for one prepared function. -/
abbrev preparedFunctionAllowance (ctx : code.Context) (length : Nat) : ChargeCounter → Nat
  | .instructions => 3*length
  | .branches => length
  | .controls => 1+length
  | .locals => ctx.locals.val.length

end Exec.Code
