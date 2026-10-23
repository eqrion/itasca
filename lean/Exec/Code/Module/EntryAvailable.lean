import Exec.Code.Module.SourceEntryPrepared
import Exec.Code.Module.PreparedEntryReplay
import Exec.Code.Module.PreparedFunctionAvailable

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent numerical resource eligibility over decoded source entry
metadata. This mentions no target callback, emitted function, or target run. -/
def EntryResourceDemand {A : Type} (budget : runtime.compiler.Budget A)
    (data : Slice U8) (env : module.Env) (index start : Usize)
    (profile : ValidationProfile) (bound : Nat) : Prop :=
  ∀ w : CodeEntry.Prepared data env index start profile,
    PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound

end Exec.Code
