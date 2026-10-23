import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Host.HostOwnership
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A checked host result closes an actual eventful machine edge. The source
trace, runtime result check, fresh certificate and raw namespace preservation
are supplied by the host dispatch lemmas; no host behavior is postulated here. -/
theorem eventful_host_return {M P F A : Type}

    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine M P view code expected)
    (afterStore : runtime.store.Store M) (afterExec : runtime.interp.Execution) (afterPlatform : P)
    (ambient : frame) (caller : Abs.AFrame) (rest : List Abs.AFrame)
    (front consumed returned : List val) (continuation : List instr) (pc : Nat)
    (source : before.source=⟨Store.decodeStore view code before.store,ambient,caller::rest,[]⟩)
    (split : caller.vals=front++consumed)
    (actual : runtime.interp.step memory hooks floats allocator before.exec before.store before.platform=
      .ok (.Ok (),afterExec,afterStore,afterPlatform))
    (retained : FrameStorePrefix before.store afterStore)
    (externs : before.store.externs.length≤afterStore.externs.length)
    (extension : Extend_store (Store.decodeStore view code before.store) (Store.decodeStore view code afterStore))
    (fresh : CertifiedSupportedStore view code afterStore)
    (checked : Abs.Ownership.ValuesOwned (Store.ownershipBounds afterStore) returned)
    (resumed : StructuredMachine.Execution view code afterStore afterExec
      ⟨Store.decodeStore view code afterStore,ambient,{caller with code:=continuation,vals:=front++returned}::rest,[]⟩ expected pc false)
    (events : List HostEvent) (count : Nat) (positive : 0<count)
    (trace : Spec.StepsHN count (Abs.decode before.source) events
      (Abs.decode ⟨Store.decodeStore view code afterStore,ambient,
        {caller with code:=continuation,vals:=front++returned}::rest,[]⟩)) :
    ∃ after : EventfulMachine M P view code expected,
      after.exec=afterExec ∧ after.store=afterStore ∧ after.platform=afterPlatform ∧
      after.source=⟨Store.decodeStore view code afterStore,ambient,
        {caller with code:=continuation,vals:=front++returned}::rest,[]⟩ ∧
      EventfulTransition memory hooks floats allocator before events after := by
  have oldOwned : Abs.Ownership.StateOwned (Store.ownershipBounds before.store)
      ⟨Store.decodeStore view code before.store,ambient,caller::rest,[]⟩ := by
    simpa only [source] using before.owned.values
  have owned := host_return_stateful_owned (continuation:=continuation) retained externs fresh.shape oldOwned split checked
  let after : EventfulMachine M P view code expected :=
    ⟨afterStore,afterExec,afterPlatform,_,pc,false,resumed,fresh,owned⟩
  refine ⟨after,rfl,rfl,rfl,rfl,actual,EventfulConcreteSim.of_steps positive trace,extension,retained,?_⟩
  change ambient=before.source.ambient
  rw [source]
end Exec.Theorems
