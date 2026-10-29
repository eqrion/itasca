import Itasca.Runtime.Store.Invariant.IssuedValues
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Interp.Relations.Arguments

/-!
Issued-value checking, decoded source typing and argument ownership. The lightweight IssuedValue contract remains independently available.
-/

/-! ## Checked Values -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Ownership checks plus issued-address provenance imply the full value
invariant used by encoding and source typing. -/
theorem IssuedValue.in_store {M : Type} {s : runtime.store.Store M} {value : runtime.Value}
    (issued : IssuedValue s value) (owner : Interp.OwnedBy s.id value) : ValueInStore s value := by
  rcases issued_value_owned_or_foreign s value issued with owned | foreign
  · exact owned
  · cases value <;> simp only [ForeignValue, Interp.OwnedBy] at foreign owner
    all_goals rename_i address
    all_goals cases address with
    | none => contradiction
    | some address => exact False.elim (foreign owner)

/-- Pointwise checked tags and ownership give typed source results. -/
theorem matched_issued_source_typed {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store))
    {values : List runtime.Value} {types : List Itasca.types.ValueType}
    (matched : List.Forall₂ (Interp.ArgumentMatches store.id) values types)
    (issued : ∀ value ∈ values, IssuedValue store value) :
    ResultsTyped (decodeStore view code store) (types.map Interp.sourceType)
      (values.map Interp.sourceValue) ∧
    (∀ value ∈ values, ValueInStore store value) ∧ types = values.map Interp.rawType := by
  revert issued
  induction matched with
  | nil => intro issued; exact ⟨.nil, by simp, rfl⟩
  | @cons value ty values types matching tail ih =>
    intro issued
    have head := (issued value (by simp)).in_store matching.1
    obtain ⟨typed, owned, tags⟩ := ih (fun value member => issued value (by simp [member]))
    refine ⟨List.Forall₂.cons ?_ typed, ?_, ?_⟩
    · rw [← matching.2]
      exact value_in_store_typed view code store sourceWf value head
    · intro v member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact owned v member
    · simp only [List.map_cons, matching.2, tags]

/-- The concrete value checker establishes specification result typing from
issued values; it does not assume the host returned correctly typed results. -/
theorem check_values_source_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (sourceWf : wf_store (decodeStore view code store))
    (values : Slice runtime.Value) (types : Slice Itasca.types.ValueType)
    (issued : ∀ value ∈ values.val, IssuedValue store value) :
    runtime.interp.check_values memory store values types ⦃ status =>
      status = .Ok () →
        ResultsTyped (decodeStore view code store) (types.val.map Interp.sourceType)
          (values.val.map Interp.sourceValue) ∧
        (∀ value ∈ values.val, ValueInStore store value) ∧
        types.val = values.val.map Interp.rawType ⦄ := by
  step with Interp.check_values_accepts_iff memory store values types as ⟨status, accepted⟩
  rename_i success
  exact matched_issued_source_typed view code store sourceWf (accepted.mp success) issued
end Itasca.Runtime.Store

end

/-! ## Issued Arguments -/

section

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

end
