import Exec.Theorems.Host.Open.Driver.ReplayCallback
import Exec.Theorems.Host.Open.Driver.ReentrantControl
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- The source/certificate part of a resumed native step. It omits the replay
dictionary's artificial call graph; actual resumption has its own graph. -/
def ResumedWorldResult {M : Type} {view : M → Slice U8} {expected : List valtype}
    (before : EventfulWorld M Unit view expected)
    (out : Answer M Unit) : Prop :=
  match out.1 with
  | .Ok _ => ∃next : EventfulWorld M Unit view expected,
      ExecutableInv view next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
      EventfulConcreteSim U32.max before.machine.pc next.machine.pc before.machine.pending next.machine.pending
        before.machine.source next.machine.source (stepHostEvents before.machine.exec before.machine.store out) ∧
      Extend_store (Store.decodeStore view before.code before.machine.store) (Store.decodeStore view next.code next.machine.store) ∧
      FrameStorePrefix before.machine.store next.machine.store ∧ before.machine.store.externs.length≤next.machine.store.externs.length ∧ next.machine.source.ambient=before.machine.source.ambient ∧
      Store.CodeAgreesOn before.machine.store before.code next.code
  | .Err error => ∃afterCode,ExecutableInv view afterCode out.2.2.1 ∧
      FrameStorePrefix before.machine.store out.2.2.1 ∧ before.machine.store.externs.length≤out.2.2.1.externs.length ∧ Store.CodeAgreesOn before.machine.store before.code afterCode ∧
      Extend_store (Store.decodeStore view before.code before.machine.store) (Store.decodeStore view afterCode out.2.2.1) ∧
      EventfulInvocationError (Abs.decode before.machine.source)
        (stepHostEvents before.machine.exec before.machine.store out)
        (Store.decodeStore view afterCode out.2.2.1) before.machine.source.ambient error

end Exec.Theorems.OpenReentrantControl
