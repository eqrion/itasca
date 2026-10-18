import Exec.Interp.Relations.TypedArguments
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- Matching value tags allow a foreign reference to reject as WrongStore;
there is no BadArguments branch. Ownership is not assumed. -/
theorem checkArguments_typed_rejection {id : Usize} {values : List runtime.Value}
    {types : List Itasca.types.ValueType} (tags : values.map rawType = types) :
    checkArguments id values types = .Ok () ∨ checkArguments id values types = .Err .WrongStore := by
  subst types
  induction values with
  | nil => exact Or.inl rfl
  | cons value values ih =>
    by_cases owned : OwnedBy id value
    · simpa only [List.map_cons,checkArguments,checkArgument,if_pos owned,ite_true] using ih
    · exact Or.inr (by simp only [List.map_cons,checkArguments,checkArgument,if_neg owned])

/-- Source typing fixes argument tags independently of reference ownership. -/
theorem typed_arguments_tags {s : _root_.store}
    {args : List runtime.Value} {types : List Itasca.types.ValueType}
    (typed : ResultsTyped s (types.map sourceType) (args.map sourceValue)) :
    args.map rawType = types := by
  apply List.map_injective_iff.mpr sourceType_injective
  have tags := Abs.results_type_of_typed typed
  simpa only [List.map_map,show Abs.valueType = Code.valueType from (funext valueType_eq_abs).symm,
    Function.comp_def,sourceValue_type] using tags

theorem typed_arguments_rejection_kind {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (source : _root_.store)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (typed : ResultsTyped source (types.val.map sourceType) (args.val.map sourceValue)) :
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref types) ⦃ status =>
      status = .Ok () ∨ status = .Err .WrongStore ⦄ := by
  have tags := typed_arguments_tags typed
  have lengths : args.val.length = types.val.length := by
    have same := congrArg List.length tags
    simpa only [List.length_map] using same
  apply WP.spec_mono (check_values_effect memory store args (alloc.vec.Vec.deref types))
  intro status result
  have same : status = checkArguments store.id args.val types.val := by
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,lengths,ite_true] using result
  rw [same]
  exact checkArguments_typed_rejection tags
end Exec.Interp
