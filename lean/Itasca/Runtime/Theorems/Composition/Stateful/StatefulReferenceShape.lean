import Itasca.Runtime.Theorems.Composition.Stateful.StatefulOwnership
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Per-kind source ownership of the exact decoded operand establishes the
runtime table reference invariant, including its full-width address word. -/
theorem owned_reference_shape {M : Type} (store : runtime.store.Store M)
    (type : Itasca.types.ElemType) (word : U64)
    (owned : Abs.Ownership.ValueOwned (ownershipBounds store) (val_ref (decodeRef type word))) :
    ReferenceShape store type word := by
  cases type <;> unfold ReferenceShape
  all_goals
    by_cases zero : word.val = 0
    · exact Or.inl zero
    · exact Or.inr (by simpa only [decodeRef,if_neg zero,val_ref,Abs.Ownership.ValueOwned,ownershipBounds] using owned)
end Itasca.Runtime.Store
