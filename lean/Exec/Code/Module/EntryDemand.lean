import Exec.Code.Module.EntryAvailable
import Exec.Code.Module.PreparedEntryUnique

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- One independently prepared source entry suffices to establish all entry
resource eligibility. Pure decoding fixes every operand of the numeric demand,
so no compiler run or universal family of callback proofs is supplied. -/
theorem EntryResourceDemand.of_prepared {A : Type} {budget : runtime.compiler.Budget A}
    {data env index start profile bound}
    (prepared : CodeEntry.Prepared data env index start profile)
    (demand : PreparedFunctionDemand budget prepared.ctx prepared.body.length
      (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands bound) :
    EntryResourceDemand budget data env index start profile bound := by
  intro other
  obtain ⟨typeEq,ctxEq,bodyEq,_,_⟩ := prepared_entry_unique prepared other
  simpa only [← typeEq,← ctxEq,← bodyEq] using demand

end Itasca.Runtime.Code
