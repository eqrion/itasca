import Itasca.Runtime.Compiler.Module.PreparedExecutableSafety
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceStepAcceptanceWasm2
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceBudgetAdvance
import Itasca.Runtime.Compiler.Module.PreparedFunctionDemand

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Source-derived conservative total charges for one prepared function. -/
abbrev preparedFunctionAllowance (ctx : code.Context) (length : Nat) : ChargeCounter → Nat
  | .instructions => 3*length
  | .branches => length
  | .controls => 1+length
  | .locals => ctx.locals.val.length

end Itasca.Runtime.Code
