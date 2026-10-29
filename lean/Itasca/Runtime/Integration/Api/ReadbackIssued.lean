import Itasca.Runtime.Interp.Invocation.ReadbackOwnership
import Itasca.Runtime.Integration.Execution.Ownership.Entry
import Itasca.Runtime.Store.Invariant.CheckedValues
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem owned_source_value_in_store {M : Type} (store : runtime.store.Store M) (value : runtime.Value)
    (owner : OwnedBy store.id value)
    (sourceOwned : Abs.Ownership.ValueOwned (Store.ownershipBounds store) (sourceValue value)) :
    Store.ValueInStore store value := by
  have issued : Store.IssuedValue store value := by
    cases value <;> try trivial
    all_goals rename_i reference
    all_goals cases reference with
    | none => trivial
    | some reference => exact fun _ => sourceOwned
  exact issued.in_store owner

end Itasca.Runtime.Theorems
