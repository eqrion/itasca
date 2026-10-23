import Exec.Generated.Equations
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

def TypeEntries {M : Type} (store : runtime.store.Store M) (source : List Itasca.types.FuncType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun ty index => store.types.val[index.val]? = some ty) source indices

end Exec.Store
