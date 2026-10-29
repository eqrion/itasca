import Itasca.Runtime.Integration.Host.HostCallSource
import Itasca.Runtime.Interp.Host.HostReturnFrames

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Successful actual host calls supply the concrete slot/frame transport used
when resuming a caller; no callback behavior is hidden in that transport. -/
theorem HostCallSourceOutcome.return_effect {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {args : List val} {base : Usize}
    {exec : runtime.interp.Execution}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    (observed : HostCallSourceOutcome view code before ambient address args base exec out)
    (success : out.1 = .Ok ()) :
    HostReturnEffect exec out.2.1 base.val (out.2.1.host_results.val.map sourceValue) := by
  obtain ⟨arguments,frames,identity,capacity,outcome⟩ := observed
  rcases outcome with returned | failed
  · obtain ⟨_,values,source,preserved⟩ := returned
    exact ⟨identity,frames,capacity,values,fun j bound below => preserved j bound (Or.inl below)⟩
  · rcases failed.1 with status | status <;> rw [success] at status <;> cases status

end Itasca.Runtime.Theorems
