import Exec.Store.Invariant.IssuedArguments
import Exec.Interp.Relations.TypedArguments
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- For values belonging to the current store, the native checker accepts
exactly the independently source-typed lists, including reference membership.
Ownership is explicit because source values erase native store identities. -/
theorem check_values_source_iff {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store)) (values : Slice runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType)
    (owned : ∀value∈values.val,ValueInStore store value) :
    runtime.interp.check_values memory store values types.deref ⦃status=>status=.Ok () ↔
      ResultsTyped (decodeStore view code store) (types.val.map sourceType) (values.val.map sourceValue)⦄ := by
  obtain ⟨status,actual,post⟩ := WP.spec_imp_exists (check_values_source_typed memory view code store sourceWf
    values types.deref (fun value member=>(owned value member).issued))
  rw [actual,WP.spec_ok]
  constructor
  · intro accepted
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using (post accepted).1
  · intro typed
    have accepted := typed_arguments_accepted memory store (decodeStore view code store) values types typed
      (fun value member=>(owned value member).1)
    simpa only [Result.ok.injEq] using (actual.symm.trans accepted)
end Exec.Store
