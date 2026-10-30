import Itasca.Runtime.Compiler.Module.SourceEntryPrepared
import Itasca.Runtime.Compiler.Module.PreparedEntryReplay
import Itasca.Runtime.Compiler.Module.PreparedFunctionAvailable

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent numerical resource eligibility over decoded source entry
metadata. This mentions no target callback, emitted function, or target run. -/
def EntryResourceDemand {A : Type} (budget : runtime.compiler.Budget A)
    (data : Slice U8) (env : metadata.Env) (index start : Usize)
    (profile : ValidationProfile) (bound : Nat) : Prop :=
  ∀ w : CodeEntry.Prepared data env index start profile,
    PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound

end Itasca.Runtime.Compiler
