import Itasca.Runtime.Theorems.Composition.StructuredHostSite
import Itasca.Runtime.Theorems.Composition.Eventful.EventfulHistory
import Itasca.Runtime.Theorems.Composition.Stateful.StatefulOwnership
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

theorem HostFrameSite.binding {M : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (site : HostFrameSite view code exec store expected ambient f rest) :
    FrameBinding store exec site.raw f := by
  have indexEq : site.index.val=exec.frames.length-1 := by have := site.last; omega
  have top : exec.frames.val.getLast?=some site.raw := by
    rw [List.getLast?_eq_getElem?]
    simpa only [indexEq] using site.frameAt
  exact (site.machine.stack.top site.raw top).binding

def HostFrameSite.eventful {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {expected : List valtype} {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame}
    (site : HostFrameSite view code exec store expected ambient f rest)
    (certified : CertifiedSupportedStore view code store) (platform : P) :
    EventfulMachine M P view code expected :=
  ⟨store,exec,platform,⟨Store.decodeStore view code store,ambient,f::rest,[]⟩,site.raw.pc.val,false,
    site.machine,certified,site.owned,certified.shape.stateful_heap_owned code⟩
end Itasca.Runtime.Theorems
