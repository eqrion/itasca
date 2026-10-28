import Itasca.Runtime.Store.Invariant.CheckedValues
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem ValueInStore.issued {M : Type} {store : runtime.store.Store M} {value : runtime.Value}
    (valid : ValueInStore store value) : IssuedValue store value := by
  cases value <;> simp only [IssuedValue,ValueInStore] at valid ⊢
  all_goals cases ‹Option _› <;> simp_all

/-- Ownership is obtained from the actual argument checker; foreign issued
references remain admissible inputs to the public rejection theorem. -/
theorem checked_arguments_owned {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store))
    (args : Slice runtime.Value) (types : Slice Itasca.types.ValueType)
    (issued : ∀ value ∈ args.val, IssuedValue store value)
    (accepted : runtime.interp.check_values memory store args types = .ok (.Ok ())) :
    ∀ value ∈ args.val, ValueInStore store value := by
  have checked := check_values_source_typed memory view code store sourceWf args types issued
  rw [accepted,WP.spec_ok] at checked
  exact (checked rfl).2.1
end Itasca.Runtime.Store
