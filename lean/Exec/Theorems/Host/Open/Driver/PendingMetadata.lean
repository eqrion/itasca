import Exec.Theorems.Host.Open.Driver.HostCompletion
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A captured source request recovers its exact raw function and signature
lookups from the decoded table and independently checked store shape. -/
theorem pending_raw_metadata {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (shape : Store.Shape view store)
    (pending : Spec.OpenHost.Pending) (address : runtime.FuncAddr)
    (beforeEq : pending.before=Store.decodeStore view code store) (addressEq : pending.address=address.index.val) :
    ∃function signature,store.funcs.val[address.index.val]?=some function ∧
      store.types.val[function.signature.val]?=some signature ∧
      pending.results=signature.results.val.map sourceType := by
  obtain ⟨sourceModule,sourceAt⟩ := pending.host
  simp only [beforeEq,addressEq,Store.decodeStore,List.getElem?_map] at sourceAt
  cases found : store.funcs.val[address.index.val]? with
  | none=>simp [found] at sourceAt
  | some function=>
    have bound := (shape.functions function (List.mem_of_getElem? found)).1
    let signature:=store.types.val[function.signature.val]
    have typed : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem bound
    exact ⟨function,signature,rfl,typed,pending_signature_results view code store pending address function signature beforeEq addressEq found typed⟩
end Exec.Theorems.OpenReentrantControl
