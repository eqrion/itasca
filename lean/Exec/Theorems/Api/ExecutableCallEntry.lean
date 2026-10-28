import Exec.Theorems.Api.ExecutableInv
import Exec.Store.Invariant.IssuedArguments

/-! Lookup evidence for an owned public function handle. This API-layer evidence
is shared by correspondence, typing and divergence; representation foundations
remain independent of public invocation setup. -/
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std

/-- The function and signature selected by one public function handle. -/
structure ExecutableCallEntry {M : Type} (store : runtime.store.Store M)
    (address : runtime.FuncAddr) where
  function : runtime.store.FuncInst
  signature : Itasca.types.FuncType
  functionLookup : store.funcs.val[address.index.val]? = some function
  signatureLookup : store.types.val[function.signature.val]? = some signature
  signatureBound : function.signature.val < store.types.val.length

/-- Issuance and ownership justify both lookups before indexing. -/
def ExecutableInv.call_entry {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (valid : ExecutableInv view code store) (address : runtime.FuncAddr)
    (issued : Store.ExternalIssued store (.Func address)) (owner : address.store = store.id) :
    ExecutableCallEntry store address := by
  have bound : address.index.val < store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val < store.types.val.length :=
    (valid.shape.functions function (List.mem_of_getElem? hf)).1
  exact ⟨function,store.types.val[function.signature.val],hf,List.getElem?_eq_getElem signatureBound,signatureBound⟩
end Itasca.Runtime.Theorems
