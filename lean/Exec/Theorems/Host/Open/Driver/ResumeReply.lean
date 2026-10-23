import Exec.Theorems.Host.Open.Driver.HostCompletion
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- The proposed host reply is checked before native continuation results are
published. A successful resumption contains exactly the accepted source reply. -/
theorem host_resume_checked_result {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (actual : hostResume memory exec store address base values status=.ok out)
    (successful : out.1=.Ok ()) :
    (checkedHostReply memory view code store signature values status).result=
      some (out.2.host_results.val.map sourceValue) := by
  have events := host_resume_events memory view code store exec address base function signature
    functionAt signatureAt values status out () actual
  simp only [hostCallEvents,successful] at events
  exact (SpecExt.HostEvent.call.inj (List.cons.inj events).1).2.2.symm
end Exec.Theorems.OpenReentrantControl
