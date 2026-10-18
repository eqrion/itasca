import Exec.Interp.Invocation.ReadbackOwnership
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Store.Invariant.CheckedValues
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

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

theorem read_results_issued {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (empty : results.val = [])
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (owned : Abs.Ownership.ValuesOwned (Store.ownershipBounds store) values)
    (represented : ValuesAt words.val 0 values) :
    runtime.interp.invoke_with_loop4 words store results 0#usize 0#usize types ⦃ out =>
      out.1 = store ∧ out.2.val.map sourceValue = values ∧
      (∀ value ∈ out.2.val, Store.ValueInStore store value) ⦄ := by
  apply WP.spec_mono (read_results_owned words store results types values empty typed wellFormed
    (fun value member => Store.owned_result_fits store value (owned value member)) represented)
  rintro ⟨after,returned⟩ ⟨sameStore,same,owners⟩
  subst after
  refine ⟨rfl,same,?_⟩
  intro value member
  apply owned_source_value_in_store store value (owners value member)
  apply owned
  rw [←same]
  exact List.mem_map.mpr ⟨value,member,rfl⟩
end Exec.Theorems
