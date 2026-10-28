import Exec.Interp.Relations.Arguments
import Exec.Interp.Control.StructuredPoint
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem sourceType_injective : Function.Injective sourceType := by
  intro left right same
  cases left <;> cases right <;> simp_all [sourceType]

theorem ValueOwnedFits.owned {id : Usize} {value : runtime.Value}
    (owned : ValueOwnedFits id value) : OwnedBy id value := by
  cases value <;> simp_all [ValueOwnedFits, OwnedBy]
  all_goals cases ‹Option _› <;> simp_all [ValueOwnedFits, OwnedBy]

/-- Source-typed arguments with issued identities satisfy the concrete checker.
This is independent of the subsequent call and interpreter execution. -/
theorem typed_arguments_match {s : _root_.store} {id : Usize}
    {args : List runtime.Value} {types : List Itasca.types.ValueType}
    (typed : ResultsTyped s (types.map sourceType) (args.map sourceValue))
    (owned : ∀ value ∈ args, ValueOwnedFits id value) :
    List.Forall₂ (ArgumentMatches id) args types := by
  have tags : args.map rawType = types := by
    apply List.map_injective_iff.mpr sourceType_injective
    have tags := Abs.results_type_of_typed typed
    simpa only [List.map_map, show Abs.valueType = Code.valueType from (funext valueType_eq_abs).symm,
      Function.comp_def, sourceValue_type] using tags
  induction args generalizing types with
  | nil => cases types <;> simp_all
  | cons value args ih =>
    cases types with
    | nil => simp at tags
    | cons ty types =>
      simp only [List.map_cons, List.cons.injEq] at tags
      apply List.Forall₂.cons
      · exact ⟨(owned value (by simp)).owned, tags.1⟩
      · apply ih
        · cases typed with | cons _ tail => exact tail
        · intro v member; exact owned v (by simp [member])
        · exact tags.2

/-- The actual argument-checking function accepts source-typed owned inputs. -/
theorem typed_arguments_accepted {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (sourceStore : _root_.store)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (typed : ResultsTyped sourceStore (types.val.map sourceType) (args.val.map sourceValue))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value) :
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) = .ok (.Ok ()) := by
  obtain ⟨answer, checked, accepted⟩ := WP.spec_imp_exists
    (check_values_accepts_iff memory store args (alloc.vec.Vec.deref types))
  have matched : List.Forall₂ (ArgumentMatches store.id) args.val (alloc.vec.Vec.deref types).val := by
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using typed_arguments_match typed owned
  have ok := accepted.mpr matched
  simpa only [ok] using checked
end Itasca.Runtime.Interp
