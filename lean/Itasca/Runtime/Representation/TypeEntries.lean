import Itasca.Runtime.Equations

/-!
Retained type-entry certificates for runtime stores. Store staging and source-capacity proofs consume the same independent signature evidence.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

def TypeEntries {M : Type} (store : runtime.store.Store M) (source : List Itasca.wasm_types.FuncType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun ty index => store.types.val[index.val]? = some ty) source indices

end Itasca.Runtime.Store
